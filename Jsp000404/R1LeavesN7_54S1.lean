import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_54S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4472000 in
theorem r1l7_11_23_L_I_M_LI_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h5 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h414 | h414
  · rcases m.htr 1 2 5 (by decide) (by decide) with h415 | h415
    · rcases m.htr 1 3 4 (by decide) (by decide) with h416 | h416
      · rcases m.htr 1 3 5 (by decide) (by decide) with h417 | h417
        · rcases m.htr 1 4 5 (by decide) (by decide) with h418 | h418
          · rcases m.htr 2 3 4 (by decide) (by decide) with h419 | h419
            · rcases m.htr 2 3 5 (by decide) (by decide) with h420 | h420
              · rcases m.htr 2 4 5 (by decide) (by decide) with h421 | h421
                · linarith only [h414, h421, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h414, h418, h419, h421, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h420, h5, hc12, hlam, hphi, ht23, u3elo4]
            · linarith only [h419, h5, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h426 | h426
            · rcases m.htr 2 3 5 (by decide) (by decide) with h427 | h427
              · rcases m.htr 2 4 5 (by decide) (by decide) with h428 | h428
                · linarith only [h0, h414, h418, h428, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h430 | h430
                  · linarith only [h414, h418, h426, h430, hlam]
                  · rcases h1bigk with h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [hlam, p432_0]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      rcases p432_3 (m.d 0 1) (by simp) with h434 | h434
                      · rcases p432_3 (m.d 1 2) (by simp) with h435 | h435
                        · linarith only [h435, hlam, p432_0]
                        · rcases p432_3 (m.d 1 3) (by simp) with h437 | h437
                          · linarith only [h1, h437, hlam]
                          · linarith only [h437, h5, hlam]
                      · linarith only [h434, hlam, p432_0]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      rcases p432_3 (m.d 0 1) (by simp) with h441 | h441
                      · rcases p432_3 (m.d 1 2) (by simp) with h442 | h442
                        · linarith only [h0, h442, hlam]
                        · rcases p432_3 (m.d 1 3) (by simp) with h444 | h444
                          · linarith only [h444, hlam, p432_0]
                          · rcases p432_3 (m.d 1 4) (by simp) with h446 | h446
                            · linarith only [h2, h446, hlam]
                            · rcases p432_3 (m.d 1 5) (by simp) with h448 | h448
                              · linarith only [h3, h448, hlam]
                              · rcases h1emin with h450 | h450 | h450 | h450 | h450
                                · rcases h3bigk with h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [hlam, p451_0]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [hc13, hlam, hphi, p451_1, u3elo0]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [hc23, hlam, hphi, p451_1, u3elo0]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    rcases p451_3 (m.d 0 3) (by simp) with h455 | h455
                                    · rcases p451_3 (m.d 1 3) (by simp) with h456 | h456
                                      · linarith only [h1, h456, hlam]
                                      · linarith only [h416, h456, hlam]
                                    · linarith only [h455, hlam, p451_0]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    rcases p451_3 (m.d 0 3) (by simp) with h460 | h460
                                    · rcases p451_3 (m.d 1 3) (by simp) with h461 | h461
                                      · linarith only [h1, h461, hlam]
                                      · linarith only [h417, h461, hlam]
                                    · linarith only [h460, hlam, p451_0]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [h1, hlam, p451_0]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [hlam, p451_0]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [h5, hlam, p451_1]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p432_1, p451_1]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [hc01, hc35, hlam, hphi, ht0b, ht5b, p432_1, p451_1]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [hc03, hlam, hphi, p451_1, u3elo2]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [hc13, hlam, hphi, p451_1, u3elo2]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [hlam, p451_0]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    rcases p451_3 (m.d 0 3) (by simp) with h473 | h473
                                    · rcases p451_3 (m.d 1 3) (by simp) with h474 | h474
                                      · linarith only [h474, h5, hlam]
                                      · linarith only [h416, h474, hlam]
                                    · linarith only [h1, h415, h426, h428, h473, h5, hlam]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    rcases p451_3 (m.d 0 3) (by simp) with h478 | h478
                                    · rcases p451_3 (m.d 1 3) (by simp) with h479 | h479
                                      · linarith only [h479, h5, hlam]
                                      · linarith only [h417, h479, hlam]
                                    · linarith only [h4, h478, hlam]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [hc03, hlam, hphi, p451_1, u3elo3]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [h416, hlam, p451_0]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [h426, hlam, p451_0]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [hlam, p451_0]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [h430, hlam, p451_1]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [h4, hlam, p451_0]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [h417, hlam, p451_0]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [h427, hlam, p451_0]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p451_1, u3elo0]
                                  · have p451_0 := h451c.1
                                    have p451_1 := h451c.2.1
                                    have p451_2 := h451c.2.2.1
                                    have p451_3 := h451c.2.2.2
                                    linarith only [hlam, p451_0]
                                · linarith only [h450, h5, hlam, ht12, ht23, u3elo1]
                                · linarith only [h450, hlam, ht12, ht23, u3elo1]
                                · linarith only [h418, h450, hc45, hlam, ht12, ht23, ht34]
                                · linarith only [h3, h4, h450, hlam, ht12, ht23, u3elo0]
                      · linarith only [h441, hlam, p432_0]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      rcases p432_3 (m.d 0 1) (by simp) with h498 | h498
                      · rcases p432_3 (m.d 1 2) (by simp) with h499 | h499
                        · linarith only [h0, h499, hlam]
                        · linarith only [h414, h499, hlam]
                      · linarith only [h498, hlam, p432_0]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      rcases p432_3 (m.d 0 1) (by simp) with h503 | h503
                      · rcases p432_3 (m.d 1 2) (by simp) with h504 | h504
                        · linarith only [h0, h504, hlam]
                        · linarith only [h415, h504, hlam]
                      · linarith only [h503, hlam, p432_0]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [h0, hlam, p432_0]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [hlam, p432_0]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [h5, hlam, p432_0]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p432_1, u3elo2]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p432_1, u3elo2]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [h1, hlam, p432_0]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [hc12, hlam, hphi, ht23, p432_1, u3elo1]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [hlam, p432_0]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      rcases p432_3 (m.d 0 1) (by simp) with h516 | h516
                      · rcases p432_3 (m.d 1 2) (by simp) with h517 | h517
                        · linarith only [h5, h517, hlam]
                        · linarith only [h414, h517, hlam]
                      · linarith only [h2, h516, hlam]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      rcases p432_3 (m.d 0 1) (by simp) with h521 | h521
                      · rcases p432_3 (m.d 1 2) (by simp) with h522 | h522
                        · linarith only [h5, h522, hlam]
                        · linarith only [h415, h522, hlam]
                      · linarith only [h3, h521, hlam]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [h2, hlam, p432_0]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [h414, hlam, p432_1]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [h416, hlam, p432_0]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [hlam, p432_0]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [h418, hlam, p432_1]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [h3, hlam, p432_0]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [h415, hlam, p432_1]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [h417, hlam, p432_0]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [h414, h415, h426, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p432_1, u3elo2]
                    · have p432_0 := h432c.1
                      have p432_1 := h432c.2.1
                      have p432_2 := h432c.2.2.1
                      have p432_3 := h432c.2.2.2
                      linarith only [hlam, p432_0]
              · linarith only [h427, h5, hc12, hlam, hphi, ht23, u3elo4]
            · linarith only [h426, h5, hc12, hlam, hphi, ht23, u3elo3]
        · linarith only [h4, h417, hc13, hlam, hphi, u3elo0]
      · linarith only [h414, h416, h5, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h540 | h540
      · rcases m.htr 1 3 5 (by decide) (by decide) with h541 | h541
        · rcases m.htr 1 4 5 (by decide) (by decide) with h542 | h542
          · linarith only [h414, h415, h542, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h544 | h544
            · rcases m.htr 2 3 5 (by decide) (by decide) with h545 | h545
              · rcases m.htr 2 4 5 (by decide) (by decide) with h546 | h546
                · linarith only [h414, h415, h542, h546, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h548 | h548
                  · linarith only [h415, h546, h548, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases h1bigk with h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [hlam, p550_0]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      rcases p550_3 (m.d 0 1) (by simp) with h552 | h552
                      · rcases p550_3 (m.d 1 2) (by simp) with h553 | h553
                        · linarith only [h553, hlam, p550_0]
                        · rcases p550_3 (m.d 1 3) (by simp) with h555 | h555
                          · linarith only [h1, h555, hlam]
                          · linarith only [h5, h555, hlam]
                      · linarith only [h552, hlam, p550_0]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      rcases p550_3 (m.d 0 1) (by simp) with h559 | h559
                      · rcases p550_3 (m.d 1 2) (by simp) with h560 | h560
                        · linarith only [h0, h560, hlam]
                        · rcases p550_3 (m.d 1 3) (by simp) with h562 | h562
                          · linarith only [h562, hlam, p550_0]
                          · rcases p550_3 (m.d 1 4) (by simp) with h564 | h564
                            · linarith only [h2, h564, hlam]
                            · rcases p550_3 (m.d 1 5) (by simp) with h566 | h566
                              · linarith only [h3, h566, hlam]
                              · rcases h1emin with h568 | h568 | h568 | h568 | h568
                                · rcases h3bigk with h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [hlam, p569_0]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [hc13, hlam, hphi, p569_1, u3elo0]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [h414, h415, h544, h545, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p569_1, u3elo0]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    rcases p569_3 (m.d 0 3) (by simp) with h573 | h573
                                    · rcases p569_3 (m.d 1 3) (by simp) with h574 | h574
                                      · linarith only [h1, h574, hlam]
                                      · linarith only [h540, h574, hlam]
                                    · linarith only [h573, hlam, p569_0]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    rcases p569_3 (m.d 0 3) (by simp) with h578 | h578
                                    · rcases p569_3 (m.d 1 3) (by simp) with h579 | h579
                                      · linarith only [h1, h579, hlam]
                                      · linarith only [h541, h579, hlam]
                                    · linarith only [h578, hlam, p569_0]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [h1, hlam, p569_0]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [hlam, p569_0]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [h5, hlam, p569_1]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p550_1, p569_1]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [h548, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p550_1, p569_1]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [hc03, hlam, hphi, p569_1, u3elo2]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [hc13, hlam, hphi, p569_1, u3elo2]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [hlam, p569_0]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    rcases p569_3 (m.d 0 3) (by simp) with h591 | h591
                                    · rcases p569_3 (m.d 1 3) (by simp) with h592 | h592
                                      · linarith only [h5, h592, hlam]
                                      · linarith only [h540, h592, hlam]
                                    · linarith only [h1, h414, h415, h541, h544, h591, hlam]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    rcases p569_3 (m.d 0 3) (by simp) with h596 | h596
                                    · rcases p569_3 (m.d 1 3) (by simp) with h597 | h597
                                      · linarith only [h5, h597, hlam]
                                      · linarith only [h541, h597, hlam]
                                    · linarith only [h4, h596, hlam]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [h414, h415, h544, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p569_1]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [h540, hlam, p569_0]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [h544, hlam, p569_0]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [hlam, p569_0]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [h548, hlam, p569_1]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [h4, hlam, p569_0]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [h541, hlam, p569_0]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [h545, hlam, p569_0]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p569_1, u3elo0]
                                  · have p569_0 := h569c.1
                                    have p569_1 := h569c.2.1
                                    have p569_2 := h569c.2.2.1
                                    have p569_3 := h569c.2.2.2
                                    linarith only [hlam, p569_0]
                                · linarith only [h415, h568, hc25, hlam, ht12]
                                · linarith only [h568, hlam, ht12, ht23, u3elo1]
                                · linarith only [h414, h5, h568, hlam, ht12, ht23, u3elo2]
                                · linarith only [h3, h4, h568, hlam, ht12, ht23, u3elo0]
                      · linarith only [h559, hlam, p550_0]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      rcases p550_3 (m.d 0 1) (by simp) with h616 | h616
                      · rcases p550_3 (m.d 1 2) (by simp) with h617 | h617
                        · linarith only [h0, h617, hlam]
                        · linarith only [h414, h617, hlam]
                      · linarith only [h616, hlam, p550_0]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      rcases p550_3 (m.d 0 1) (by simp) with h621 | h621
                      · rcases p550_3 (m.d 1 2) (by simp) with h622 | h622
                        · linarith only [h0, h622, hlam]
                        · rcases p550_3 (m.d 1 3) (by simp) with h624 | h624
                          · linarith only [h1, h624, hlam]
                          · linarith only [h541, h624, hlam]
                      · linarith only [h621, hlam, p550_0]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [h0, hlam, p550_0]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [hlam, p550_0]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [h5, hlam, p550_0]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [h415, h545, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p550_1, u3elo2]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [h415, hlam, p550_0]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [h1, hlam, p550_0]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [h414, h544, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p550_1, u3elo1]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [hlam, p550_0]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      rcases p550_3 (m.d 0 1) (by simp) with h636 | h636
                      · rcases p550_3 (m.d 1 2) (by simp) with h637 | h637
                        · linarith only [h5, h637, hlam]
                        · linarith only [h414, h637, hlam]
                      · linarith only [h2, h636, hlam]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [h1, h414, h415, h544, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p550_1, u3elo0]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [h2, hlam, p550_0]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [h414, hlam, p550_1]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [h540, hlam, p550_0]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [hlam, p550_0]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [h542, hlam, p550_1]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [h3, hlam, p550_0]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [h3, h414, h544, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p550_1]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [h541, hlam, p550_0]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      rcases p550_3 (m.d 0 1) (by simp) with h650 | h650
                      · rcases p550_3 (m.d 1 2) (by simp) with h651 | h651
                        · linarith only [h415, h651, hlam]
                        · linarith only [h414, h651, hlam]
                      · linarith only [h2, h650, hlam]
                    · have p550_0 := h550c.1
                      have p550_1 := h550c.2.1
                      have p550_2 := h550c.2.2.1
                      have p550_3 := h550c.2.2.2
                      linarith only [hlam, p550_0]
              · linarith only [h1, h541, h545, hc23, hlam, hphi, u3elo0]
            · linarith only [h5, h544, hc12, hlam, hphi, ht23, u3elo3]
        · linarith only [h4, h541, hc13, hlam, hphi, u3elo0]
      · linarith only [h414, h5, h540, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h660 | h660
    · rcases m.htr 1 3 4 (by decide) (by decide) with h661 | h661
      · rcases m.htr 1 3 5 (by decide) (by decide) with h662 | h662
        · rcases m.htr 1 4 5 (by decide) (by decide) with h663 | h663
          · rcases m.htr 2 3 4 (by decide) (by decide) with h664 | h664
            · rcases m.htr 2 3 5 (by decide) (by decide) with h665 | h665
              · rcases m.htr 2 4 5 (by decide) (by decide) with h666 | h666
                · rcases m.htr 3 4 5 (by decide) (by decide) with h667 | h667
                  · rcases h1bigk with h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      rcases p668_3 (m.d 0 1) (by simp) with h670 | h670
                      · rcases p668_3 (m.d 1 2) (by simp) with h671 | h671
                        · linarith only [h671, hlam, p668_0]
                        · rcases p668_3 (m.d 1 3) (by simp) with h673 | h673
                          · linarith only [h1, h673, hlam]
                          · linarith only [h5, h673, hlam]
                      · linarith only [h670, hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h661, h667, hc01, hc45, hlam, hphi, ht0b, ht5b, p668_1]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      rcases p668_3 (m.d 0 1) (by simp) with h678 | h678
                      · rcases p668_3 (m.d 1 2) (by simp) with h679 | h679
                        · linarith only [h0, h679, hlam]
                        · rcases p668_3 (m.d 1 3) (by simp) with h681 | h681
                          · linarith only [h1, h681, hlam]
                          · linarith only [h661, h681, hlam]
                      · linarith only [h678, hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      rcases p668_3 (m.d 0 1) (by simp) with h685 | h685
                      · rcases p668_3 (m.d 1 2) (by simp) with h686 | h686
                        · linarith only [h0, h686, hlam]
                        · linarith only [h660, h686, hlam]
                      · linarith only [h685, hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h0, hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h5, hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h414, hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h414, h664, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p668_1, u3elo2]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h1, hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h1, hc12, hlam, hphi, ht23, p668_1, u3elo0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h1, h414, h660, h665, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p668_1, u3elo0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      rcases p668_3 (m.d 0 1) (by simp) with h699 | h699
                      · rcases p668_3 (m.d 1 2) (by simp) with h700 | h700
                        · linarith only [h5, h700, hlam]
                        · linarith only [h660, h700, hlam]
                      · linarith only [h3, h699, hlam]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h2, hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h2, h660, h665, h667, hc01, hc45, hlam, hphi, ht0b, ht5b, p668_1]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h661, hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      rcases p668_3 (m.d 0 1) (by simp) with h708 | h708
                      · rcases p668_3 (m.d 1 2) (by simp) with h709 | h709
                        · linarith only [h414, h709, hlam]
                        · linarith only [h660, h709, hlam]
                      · linarith only [h3, h708, hlam]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h3, hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h660, hlam, p668_1]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h662, hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h663, hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [hlam, p668_0]
                  · linarith only [h5, h660, h666, h667, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h3, h414, h660, h663, h666, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h414, h660, h664, h665, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
            · linarith only [h5, h660, h664, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
          · linarith only [h414, h660, h663, hlam]
        · linarith only [h4, h662, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h724 | h724
        · rcases m.htr 1 4 5 (by decide) (by decide) with h725 | h725
          · rcases m.htr 2 3 4 (by decide) (by decide) with h726 | h726
            · linarith only [h5, h660, h661, h726, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h5, h660, h726, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
          · linarith only [h5, h660, h661, h725, hlam]
        · linarith only [h4, h5, h660, h724, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h731 | h731
      · rcases m.htr 1 3 5 (by decide) (by decide) with h732 | h732
        · rcases m.htr 1 4 5 (by decide) (by decide) with h733 | h733
          · rcases m.htr 2 3 4 (by decide) (by decide) with h734 | h734
            · rcases m.htr 2 3 5 (by decide) (by decide) with h735 | h735
              · rcases m.htr 2 4 5 (by decide) (by decide) with h736 | h736
                · rcases m.htr 3 4 5 (by decide) (by decide) with h737 | h737
                  · rcases h1bigk with h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [hlam, p738_0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      rcases p738_3 (m.d 0 1) (by simp) with h740 | h740
                      · rcases p738_3 (m.d 1 2) (by simp) with h741 | h741
                        · linarith only [h741, hlam, p738_0]
                        · rcases p738_3 (m.d 1 3) (by simp) with h743 | h743
                          · linarith only [h1, h743, hlam]
                          · linarith only [h5, h743, hlam]
                      · linarith only [h740, hlam, p738_0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [h731, h737, hc01, hc45, hlam, hphi, ht0b, ht5b, p738_1]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      rcases p738_3 (m.d 0 1) (by simp) with h748 | h748
                      · rcases p738_3 (m.d 1 2) (by simp) with h749 | h749
                        · linarith only [h0, h749, hlam]
                        · rcases p738_3 (m.d 1 3) (by simp) with h751 | h751
                          · linarith only [h1, h751, hlam]
                          · linarith only [h731, h751, hlam]
                      · linarith only [h748, hlam, p738_0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      rcases p738_3 (m.d 0 1) (by simp) with h755 | h755
                      · rcases p738_3 (m.d 1 2) (by simp) with h756 | h756
                        · linarith only [h0, h756, hlam]
                        · rcases p738_3 (m.d 1 3) (by simp) with h758 | h758
                          · linarith only [h1, h758, hlam]
                          · linarith only [h732, h758, hlam]
                      · linarith only [h755, hlam, p738_0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [h0, hlam, p738_0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [hlam, p738_0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [h5, hlam, p738_0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [h414, hlam, p738_0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [h660, hlam, p738_0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [h1, hlam, p738_0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [hc12, hlam, hphi, ht23, p738_1, u3elo1]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [hlam, p738_0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [h1, h660, h733, hc12, hlam, hphi, ht23, p738_1, u3elo0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [h1, h660, hc12, hlam, hphi, ht23, p738_1, u3elo0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [h2, hlam, p738_0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [h1, h731, hc12, hlam, hphi, ht23, p738_1, u3elo0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [h731, hlam, p738_0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [hlam, p738_0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [h1, h660, h731, hc12, hlam, hphi, ht23, p738_1, u3elo0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [h3, hlam, p738_0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [h3, h4, hc12, hlam, hphi, ht23, p738_1, u3elo0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [h732, hlam, p738_0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [h733, hlam, p738_0]
                    · have p738_0 := h738c.1
                      have p738_1 := h738c.2.1
                      have p738_2 := h738c.2.2.1
                      have p738_3 := h738c.2.2.2
                      linarith only [hlam, p738_0]
                  · rcases h1bigk with h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [hlam, p782_0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      rcases p782_3 (m.d 0 1) (by simp) with h784 | h784
                      · rcases p782_3 (m.d 1 2) (by simp) with h785 | h785
                        · linarith only [h785, hlam, p782_0]
                        · rcases p782_3 (m.d 1 3) (by simp) with h787 | h787
                          · linarith only [h1, h787, hlam]
                          · linarith only [h5, h787, hlam]
                      · linarith only [h784, hlam, p782_0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h731, h733, h737, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p782_1]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h733, h737, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p782_1]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      rcases p782_3 (m.d 0 1) (by simp) with h793 | h793
                      · rcases p782_3 (m.d 1 2) (by simp) with h794 | h794
                        · linarith only [h0, h794, hlam]
                        · rcases p782_3 (m.d 1 3) (by simp) with h796 | h796
                          · linarith only [h1, h796, hlam]
                          · linarith only [h732, h796, hlam]
                      · linarith only [h793, hlam, p782_0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h0, hlam, p782_0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [hlam, p782_0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h5, hlam, p782_0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h414, hlam, p782_0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h660, hlam, p782_0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h1, hlam, p782_0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h1, hc12, hlam, hphi, ht23, p782_1, u3elo0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [hlam, p782_0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h1, h733, h737, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p782_1, u3elo0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h1, h660, hc12, hlam, hphi, ht23, p782_1, u3elo0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h2, hlam, p782_0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h1, h731, hc12, hlam, hphi, ht23, p782_1, u3elo0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h731, hlam, p782_0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [hlam, p782_0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h1, h660, h731, hc12, hlam, hphi, ht23, p782_1, u3elo0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h3, hlam, p782_0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h3, h4, hc12, hlam, hphi, ht23, p782_1, u3elo0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h732, hlam, p782_0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [h733, hlam, p782_0]
                    · have p782_0 := h782c.1
                      have p782_1 := h782c.2.1
                      have p782_2 := h782c.2.2.1
                      have p782_3 := h782c.2.2.2
                      linarith only [hlam, p782_0]
                · linarith only [h414, h733, h736, hlam]
              · linarith only [h5, h732, h735, hlam]
            · linarith only [h5, h734, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h823 | h823
            · rcases m.htr 2 3 5 (by decide) (by decide) with h824 | h824
              · rcases m.htr 2 4 5 (by decide) (by decide) with h825 | h825
                · linarith only [h414, h733, h823, h825, hc12, hlam, hphi, ht23, u3elo2]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h827 | h827
                  · linarith only [h414, h825, h827, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases h1bigk with h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [hlam, p829_0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      rcases p829_3 (m.d 0 1) (by simp) with h831 | h831
                      · rcases p829_3 (m.d 1 2) (by simp) with h832 | h832
                        · linarith only [h832, hlam, p829_0]
                        · rcases p829_3 (m.d 1 3) (by simp) with h834 | h834
                          · linarith only [h1, h834, hlam]
                          · linarith only [h5, h834, hlam]
                      · linarith only [h831, hlam, p829_0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      rcases p829_3 (m.d 0 1) (by simp) with h838 | h838
                      · rcases p829_3 (m.d 1 2) (by simp) with h839 | h839
                        · linarith only [h0, h839, hlam]
                        · rcases p829_3 (m.d 1 3) (by simp) with h841 | h841
                          · linarith only [h841, hlam, p829_0]
                          · rcases p829_3 (m.d 1 4) (by simp) with h843 | h843
                            · linarith only [h2, h843, hlam]
                            · rcases p829_3 (m.d 1 5) (by simp) with h845 | h845
                              · linarith only [h3, h845, hlam]
                              · rcases h1emin with h847 | h847 | h847 | h847 | h847
                                · rcases h3bigk with h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [hc13, hlam, hphi, p848_1, u3elo0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [hc23, hlam, hphi, p848_1, u3elo0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    rcases p848_3 (m.d 0 3) (by simp) with h852 | h852
                                    · rcases p848_3 (m.d 1 3) (by simp) with h853 | h853
                                      · linarith only [h1, h853, hlam]
                                      · linarith only [h731, h853, hlam]
                                    · linarith only [h852, hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    rcases p848_3 (m.d 0 3) (by simp) with h857 | h857
                                    · rcases p848_3 (m.d 1 3) (by simp) with h858 | h858
                                      · linarith only [h1, h858, hlam]
                                      · linarith only [h732, h858, hlam]
                                    · linarith only [h857, hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h1, hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h5, hlam, p848_1]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p829_1, p848_1]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h827, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p829_1, p848_1]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [hc03, hlam, hphi, p848_1, u3elo2]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [hc13, hlam, hphi, p848_1, u3elo2]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    rcases p848_3 (m.d 0 3) (by simp) with h870 | h870
                                    · rcases p848_3 (m.d 1 3) (by simp) with h871 | h871
                                      · linarith only [h5, h871, hlam]
                                      · linarith only [h731, h871, hlam]
                                    · linarith only [h870, hc03, hlam, hphi, p848_1, u3elo2]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    rcases p848_3 (m.d 0 3) (by simp) with h875 | h875
                                    · rcases p848_3 (m.d 1 3) (by simp) with h876 | h876
                                      · linarith only [h5, h876, hlam]
                                      · linarith only [h732, h876, hlam]
                                    · linarith only [h4, h875, hlam]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [hc03, hlam, hphi, p848_1, u3elo3]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h731, hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h823, hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h827, hlam, p848_1]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h4, hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h732, hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h824, hlam, p848_0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [h1, h732, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p848_1, u3elo0]
                                  · have p848_0 := h848c.1
                                    have p848_1 := h848c.2.1
                                    have p848_2 := h848c.2.2.1
                                    have p848_3 := h848c.2.2.2
                                    linarith only [hlam, p848_0]
                                · linarith only [h414, h847, hc24, hlam, ht12]
                                · linarith only [h1, h847, hlam, ht12, ht23, u3elo0]
                                · linarith only [h3, h4, h733, h847, hlam, ht12, ht23, u3elo0]
                                · linarith only [h3, h4, h847, hlam, ht12, ht23, u3elo0]
                      · linarith only [h838, hlam, p829_0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      rcases p829_3 (m.d 0 1) (by simp) with h895 | h895
                      · rcases p829_3 (m.d 1 2) (by simp) with h896 | h896
                        · linarith only [h0, h896, hlam]
                        · rcases p829_3 (m.d 1 3) (by simp) with h898 | h898
                          · linarith only [h1, h898, hlam]
                          · linarith only [h731, h898, hlam]
                      · linarith only [h895, hlam, p829_0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      rcases p829_3 (m.d 0 1) (by simp) with h902 | h902
                      · rcases p829_3 (m.d 1 2) (by simp) with h903 | h903
                        · linarith only [h0, h903, hlam]
                        · rcases p829_3 (m.d 1 3) (by simp) with h905 | h905
                          · linarith only [h1, h905, hlam]
                          · linarith only [h732, h905, hlam]
                      · linarith only [h902, hlam, p829_0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [h0, hlam, p829_0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [hlam, p829_0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [h5, hlam, p829_0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [h414, hlam, p829_0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [h660, hlam, p829_0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [h1, hlam, p829_0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [hc12, hlam, hphi, ht23, p829_1, u3elo1]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [hlam, p829_0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [h1, h414, hc12, hlam, hphi, ht23, p829_1, u3elo0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [h1, h660, hc12, hlam, hphi, ht23, p829_1, u3elo0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [h2, hlam, p829_0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [h414, h824, h825, hc12, hlam, hphi, ht23, p829_1, u3elo2]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [h731, hlam, p829_0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [hlam, p829_0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [h733, hlam, p829_1]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [h3, hlam, p829_0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [h3, h4, hc12, hlam, hphi, ht23, p829_1, u3elo0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [h732, hlam, p829_0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [h3, h4, h414, hc12, hlam, hphi, ht23, p829_1, u3elo0]
                    · have p829_0 := h829c.1
                      have p829_1 := h829c.2.1
                      have p829_2 := h829c.2.2.1
                      have p829_3 := h829c.2.2.2
                      linarith only [hlam, p829_0]
              · linarith only [h1, h732, h824, hc23, hlam, hphi, u3elo0]
            · linarith only [h5, h823, hc12, hlam, hphi, ht23, u3elo3]
        · linarith only [h4, h732, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h932 | h932
        · rcases m.htr 1 4 5 (by decide) (by decide) with h933 | h933
          · rcases m.htr 2 3 4 (by decide) (by decide) with h934 | h934
            · linarith only [h731, h932, h934, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h5, h934, hc12, hlam, hphi, ht23, u3elo3]
          · linarith only [h731, h932, h933, hlam]
        · linarith only [h4, h932, hc13, hlam, hphi, u3elo0]

set_option maxHeartbeats 4472000 in
theorem r1l7_11_23_L_I_M_LI_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
  · exact r1l7_11_23_L_I_M_LI_x0_x0_x0_x0_x0_x0 m hb1 hb3 h0 h1 h2 h3 h4 h5
  · exact r1l7_11_23_L_I_M_LI_x0_x0_x0_x0_x0_x1 m hb1 hb3 h0 h1 h2 h3 h4 h5

end R2N4
