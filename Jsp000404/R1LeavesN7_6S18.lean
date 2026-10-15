import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S17

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6528000 in
set_option maxHeartbeats 6528000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s8 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h6793 := hg6793
  rcases m.htr 0 1 4 (by decide) (by decide) with h6794 | h6794
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9 m hb0 hb2 hb4 h0 h6793 h6794
  · rcases m.htr 0 1 5 (by decide) (by decide) with h9433 | h9433
    · rcases m.htr 0 2 3 (by decide) (by decide) with h9434 | h9434
      · rcases m.htr 0 2 4 (by decide) (by decide) with h9435 | h9435
        · rcases m.htr 0 2 5 (by decide) (by decide) with h9436 | h9436
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9437 | h9437
            · linarith only [h6793, h6794, h9437, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9439 | h9439
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9440 | h9440
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9441 | h9441
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9442 | h9442
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9443 | h9443
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9444 | h9444
                        · linarith only [h6793, h9437, h9444, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9446 | h9446
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h9447 | h9447
                            · linarith only [h6793, h6794, h9441, h9444, h9447, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h9449 | h9449
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h9450 | h9450
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h9451 | h9451
                                  · rcases h0bigk with h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c | h9452c
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [hlam, p9452_0]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [h0, hlam, p9452_1]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [h6794, h9444, hc03, hc34, hlam, hphi, p9452_1]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [h6794, hlam, p9452_1]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      rcases p9452_3 (m.d 0 1) (by simp) with h9457 | h9457
                                      · rcases p9452_3 (m.d 0 2) (by simp) with h9458 | h9458
                                        · rcases p9452_3 (m.d 0 3) (by simp) with h9459 | h9459
                                          · linarith only [h6793, h9459, hlam]
                                          · linarith only [h9439, h9459, hlam]
                                        · linarith only [h9436, h9458, hlam]
                                      · linarith only [h9433, h9457, hlam]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [h6793, h9441, h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9452_1, u0elo1]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [hlam, p9452_0]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [h6793, h9441, h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9452_1, u0elo1]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [h6793, h6794, h9441, h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9452_1, u0elo1]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      rcases p9452_3 (m.d 0 1) (by simp) with h9468 | h9468
                                      · linarith only [h0, h9468, hlam]
                                      · linarith only [h9433, h9468, hlam]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [h6793, hlam, p9452_1]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [h9434, hlam, p9452_1]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [hlam, p9452_0]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [h9437, hlam, p9452_1]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      rcases p9452_3 (m.d 0 1) (by simp) with h9475 | h9475
                                      · rcases p9452_3 (m.d 0 2) (by simp) with h9476 | h9476
                                        · rcases p9452_3 (m.d 0 3) (by simp) with h9477 | h9477
                                          · rcases p9452_3 (m.d 0 4) (by simp) with h9478 | h9478
                                            · rcases p9452_3 (m.d 0 5) (by simp) with h9479 | h9479
                                              · linarith only [h9439, h9479, hlam]
                                              · rcases h0emin with h9481 | h9481 | h9481 | h9481 | h9481
                                                · rcases h2bigk with h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c | h9482c
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [hlam, p9482_0]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [h0, hlam, p9482_1]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9482_1, u0elo1]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [h9447, h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9482_1, u0elo1]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    rcases p9482_3 (m.d 0 2) (by simp) with h9487 | h9487
                                                    · rcases p9482_3 (m.d 1 2) (by simp) with h9488 | h9488
                                                      · rcases p9482_3 (m.d 2 3) (by simp) with h9489 | h9489
                                                        · linarith only [h9434, h9489, hlam]
                                                        · linarith only [h9449, h9489, hlam]
                                                      · linarith only [h9443, h9488, hlam]
                                                    · linarith only [h9487, hlam, p9482_0]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [h0, h6793, h9433, h9443, h9449, h9451, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9452_1, p9482_1]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [hlam, p9482_0]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    rcases p9482_3 (m.d 0 2) (by simp) with h9496 | h9496
                                                    · linarith only [h0, h9496, hlam]
                                                    · linarith only [h9434, h9496, hlam]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    rcases p9482_3 (m.d 0 2) (by simp) with h9499 | h9499
                                                    · linarith only [h0, h9499, hlam]
                                                    · linarith only [h9435, h9499, hlam]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [h0, h6793, h9433, h9443, hlam, p9452_1, p9482_2]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [h9434, hlam, p9482_0]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [h9441, hlam, p9482_0]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [hlam, p9482_0]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [h9447, hlam, p9482_0]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [h6793, h9441, h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9482_1, u0elo0]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [h9435, hlam, p9482_0]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [h9442, hlam, p9482_0]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [h9435, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9482_1, u0elo1]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [hlam, p9482_0]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [h9435, h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9482_1, u0elo1]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [h9436, hlam, p9482_0]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [h9443, hlam, p9482_0]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [h9449, hlam, p9482_1]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [h9450, hlam, p9482_0]
                                                  · have p9482_0 := h9482c.1
                                                    have p9482_1 := h9482c.2.1
                                                    have p9482_2 := h9482c.2.2.1
                                                    have p9482_3 := h9482c.2.2.2
                                                    linarith only [hlam, p9482_0]
                                                · rcases h2bigk with h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c | h9518c
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [hlam, p9518_0]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [h0, hlam, p9518_1]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9518_1, u0elo1]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [h9447, h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9518_1, u0elo1]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    rcases p9518_3 (m.d 0 2) (by simp) with h9523 | h9523
                                                    · rcases p9518_3 (m.d 1 2) (by simp) with h9524 | h9524
                                                      · rcases p9518_3 (m.d 2 3) (by simp) with h9525 | h9525
                                                        · linarith only [h9434, h9525, hlam]
                                                        · linarith only [h9449, h9525, hlam]
                                                      · linarith only [h9443, h9524, hlam]
                                                    · linarith only [h9523, hlam, p9518_0]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [h9481, hc12, hlam, ht01, p9518_1]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [hlam, p9518_0]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    rcases p9518_3 (m.d 0 2) (by simp) with h9532 | h9532
                                                    · linarith only [h0, h9532, hlam]
                                                    · linarith only [h9434, h9532, hlam]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    rcases p9518_3 (m.d 0 2) (by simp) with h9535 | h9535
                                                    · linarith only [h0, h9535, hlam]
                                                    · linarith only [h9435, h9535, hlam]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [h0, h6793, h9433, h9443, hlam, p9452_1, p9518_2]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [h9434, hlam, p9518_0]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [h9441, hlam, p9518_0]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [hlam, p9518_0]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [h9447, hlam, p9518_0]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [h9434, h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9518_1, u0elo1]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [h9435, hlam, p9518_0]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [h9442, hlam, p9518_0]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [h6793, h6794, h9433, h9435, h9443, h9444, h9449, h9451, hc23, hc34, hc45, hlam, hphi, ht0b, ht5b, p9452_1, p9518_1, u0elo1]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [hlam, p9518_0]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [h9435, h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9518_1, u0elo1]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [h9436, hlam, p9518_0]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [h9443, hlam, p9518_0]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [h9449, hlam, p9518_1]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [h9450, hlam, p9518_0]
                                                  · have p9518_0 := h9518c.1
                                                    have p9518_1 := h9518c.2.1
                                                    have p9518_2 := h9518c.2.2.1
                                                    have p9518_3 := h9518c.2.2.2
                                                    linarith only [hlam, p9518_0]
                                                · rcases h2bigk with h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c | h9554c
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [hlam, p9554_0]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [h0, hlam, p9554_1]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9554_1, u0elo1]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [h9447, h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9554_1, u0elo1]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    rcases p9554_3 (m.d 0 2) (by simp) with h9559 | h9559
                                                    · rcases p9554_3 (m.d 1 2) (by simp) with h9560 | h9560
                                                      · rcases p9554_3 (m.d 2 3) (by simp) with h9561 | h9561
                                                        · linarith only [h9434, h9561, hlam]
                                                        · linarith only [h9449, h9561, hlam]
                                                      · linarith only [h9443, h9560, hlam]
                                                    · linarith only [h9559, hlam, p9554_0]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [h0, h6793, h9433, h9443, h9449, h9451, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9452_1, p9554_1]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [hlam, p9554_0]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    rcases p9554_3 (m.d 0 2) (by simp) with h9568 | h9568
                                                    · linarith only [h0, h9568, hlam]
                                                    · linarith only [h9434, h9568, hlam]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    rcases p9554_3 (m.d 0 2) (by simp) with h9571 | h9571
                                                    · linarith only [h0, h9571, hlam]
                                                    · linarith only [h9435, h9571, hlam]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [h0, h6793, h9433, h9443, hlam, p9452_1, p9554_2]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [h9434, hlam, p9554_0]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [h9441, hlam, p9554_0]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [hlam, p9554_0]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [h9447, hlam, p9554_0]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [h9434, h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9554_1, u0elo1]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [h9435, hlam, p9554_0]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [h9442, hlam, p9554_0]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [h6793, h6794, h9433, h9435, h9443, h9444, h9449, h9451, hc23, hc34, hc45, hlam, hphi, ht0b, ht5b, p9452_1, p9554_1, u0elo1]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [hlam, p9554_0]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [h9435, h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9554_1, u0elo1]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [h9436, hlam, p9554_0]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [h9443, hlam, p9554_0]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [h9449, hlam, p9554_1]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [h9450, hlam, p9554_0]
                                                  · have p9554_0 := h9554c.1
                                                    have p9554_1 := h9554c.2.1
                                                    have p9554_2 := h9554c.2.2.1
                                                    have p9554_3 := h9554c.2.2.2
                                                    linarith only [hlam, p9554_0]
                                                · rcases h2bigk with h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c | h9590c
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [hlam, p9590_0]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [h0, hlam, p9590_1]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9590_1, u0elo1]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [h9447, h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9590_1, u0elo1]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    rcases p9590_3 (m.d 0 2) (by simp) with h9595 | h9595
                                                    · rcases p9590_3 (m.d 1 2) (by simp) with h9596 | h9596
                                                      · rcases p9590_3 (m.d 2 3) (by simp) with h9597 | h9597
                                                        · linarith only [h9434, h9597, hlam]
                                                        · linarith only [h9449, h9597, hlam]
                                                      · linarith only [h9443, h9596, hlam]
                                                    · linarith only [h9595, hlam, p9590_0]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [h0, h6793, h9433, h9443, h9449, h9451, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9452_1, p9590_1]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [hlam, p9590_0]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    rcases p9590_3 (m.d 0 2) (by simp) with h9604 | h9604
                                                    · linarith only [h0, h9604, hlam]
                                                    · linarith only [h9434, h9604, hlam]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    rcases p9590_3 (m.d 0 2) (by simp) with h9607 | h9607
                                                    · linarith only [h0, h9607, hlam]
                                                    · linarith only [h9435, h9607, hlam]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [h0, h6793, h9433, h9443, hlam, p9452_1, p9590_2]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [h9434, hlam, p9590_0]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [h9441, hlam, p9590_0]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [hlam, p9590_0]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [h9447, hlam, p9590_0]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [h9434, h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9590_1, u0elo1]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [h9435, hlam, p9590_0]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [h9442, hlam, p9590_0]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [h6793, h6794, h9433, h9435, h9443, h9444, h9449, h9451, hc23, hc34, hc45, hlam, hphi, ht0b, ht5b, p9452_1, p9590_1, u0elo1]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [hlam, p9590_0]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [h9435, h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9590_1, u0elo1]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [h9436, hlam, p9590_0]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [h9443, hlam, p9590_0]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [h9449, hlam, p9590_1]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [h9450, hlam, p9590_0]
                                                  · have p9590_0 := h9590c.1
                                                    have p9590_1 := h9590c.2.1
                                                    have p9590_2 := h9590c.2.2.1
                                                    have p9590_3 := h9590c.2.2.2
                                                    linarith only [hlam, p9590_0]
                                                · linarith only [h6793, h6794, h9444, h9481, hc34, hlam, ht01, ht12, ht23, p9452_1]
                                            · linarith only [h9440, h9478, hlam]
                                          · linarith only [h9439, h9477, hlam]
                                        · linarith only [h9436, h9476, hlam]
                                      · linarith only [h9433, h9475, hlam]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [h6793, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p9452_1, u0elo3]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [h9435, hlam, p9452_0]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [h9434, h9449, h9451, hc45, hlam, hphi, ht0b, ht5b, p9452_1, u0elo3]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [hlam, p9452_0]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      rcases p9452_3 (m.d 0 1) (by simp) with h9635 | h9635
                                      · linarith only [h6794, h9635, hlam]
                                      · linarith only [h9433, h9635, hlam]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [h9433, hlam, p9452_0]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [h9436, hlam, p9452_1]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [h9439, hlam, p9452_0]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [h9440, hlam, p9452_1]
                                    · have p9452_0 := h9452c.1
                                      have p9452_1 := h9452c.2.1
                                      have p9452_2 := h9452c.2.2.1
                                      have p9452_3 := h9452c.2.2.2
                                      linarith only [hlam, p9452_0]
                                  · linarith only [h6793, h6794, h9444, h9451, hc13, hc45, hlam, hphi, ht34]
                                · linarith only [h6794, h9433, h9444, h9446, h9447, h9449, h9450, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h6793, h6794, h9439, h9444, h9449, hc23, hc34, hlam, hphi]
                          · linarith only [h6793, h6794, h9446, hc13, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h9436, h9443, hlam]
                    · linarith only [h0, h9435, h9442, hlam]
                  · linarith only [h0, h9434, h9441, hlam]
                · linarith only [h6794, h9433, h9440, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9651 | h9651
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9652 | h9652
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9653 | h9653
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9654 | h9654
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9655 | h9655
                        · linarith only [h6793, h9437, h9655, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9657 | h9657
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h9658 | h9658
                            · linarith only [h6793, h6794, h9433, h9652, h9655, h9658, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h9660 | h9660
                              · linarith only [h6793, h9439, h9652, h9660, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h9662 | h9662
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h9663 | h9663
                                  · rcases h0bigk with h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c | h9664c
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [hlam, p9664_0]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [h0, hlam, p9664_1]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [h6794, h9655, hc03, hc34, hlam, hphi, p9664_1]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [h6794, hlam, p9664_1]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [h6794, h9433, h9654, h9655, h9660, hc23, hc34, hlam, hphi, p9664_1]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [h6793, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p9664_1, u0elo1]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [hlam, p9664_0]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      rcases p9664_3 (m.d 0 1) (by simp) with h9672 | h9672
                                      · linarith only [h0, h9672, hlam]
                                      · linarith only [h6793, h9672, hlam]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [h6794, h9433, h9654, h9660, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9664_1, u0elo1]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      rcases p9664_3 (m.d 0 1) (by simp) with h9676 | h9676
                                      · linarith only [h0, h9676, hlam]
                                      · linarith only [h9433, h9676, hlam]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [h6793, hlam, p9664_1]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [h9434, hlam, p9664_1]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [hlam, p9664_0]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [h9437, hlam, p9664_1]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [h9439, hlam, p9664_1]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [h9433, h9654, h9660, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9664_1, u0elo3]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [h9435, hlam, p9664_0]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      rcases p9664_3 (m.d 0 1) (by simp) with h9686 | h9686
                                      · linarith only [h6794, h9686, hlam]
                                      · linarith only [h6793, h9686, hlam]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [hlam, p9664_0]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      rcases p9664_3 (m.d 0 1) (by simp) with h9690 | h9690
                                      · linarith only [h6794, h9690, hlam]
                                      · linarith only [h9433, h9690, hlam]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [h9433, hlam, p9664_0]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [h9436, hlam, p9664_1]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [h6793, h6794, h9433, h9652, h9655, hc23, hc34, hlam, hphi, p9664_1]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [h9651, hlam, p9664_1]
                                    · have p9664_0 := h9664c.1
                                      have p9664_1 := h9664c.2.1
                                      have p9664_2 := h9664c.2.2.1
                                      have p9664_3 := h9664c.2.2.2
                                      linarith only [hlam, p9664_0]
                                  · linarith only [h6794, h9655, h9662, h9663, hc01, hc24, hlam, hphi, ht12]
                                · linarith only [h6794, h9433, h9655, h9657, h9658, h9662, hc23, hc34, hlam, hphi]
                          · linarith only [h6793, h6794, h9652, h9657, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h9436, h9654, hlam]
                    · linarith only [h0, h9435, h9653, hlam]
                  · linarith only [h0, h9434, h9652, hlam]
                · linarith only [h6794, h9433, h9651, hlam]
          · linarith only [h0, h9433, h9436, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h9706 | h9706
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9707 | h9707
            · linarith only [h0, h6793, h9435, h9707, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9709 | h9709
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9710 | h9710
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9711 | h9711
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9712 | h9712
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9713 | h9713
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9714 | h9714
                        · linarith only [h0, h6793, h9435, h9707, h9712, h9714, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9716 | h9716
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h9717 | h9717
                            · linarith only [h0, h6793, h9435, h9711, h9712, h9714, h9717, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h9719 | h9719
                              · linarith only [h0, h6793, h9435, h9711, h9712, h9719, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h0, h6793, h9435, h9709, h9712, h9719, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h0, h6793, h9435, h9712, h9716, hc13, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h9435, h9712, h9713, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9724 | h9724
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9725 | h9725
                        · linarith only [h0, h6793, h9435, h9707, h9712, h9725, hc02, hc24, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9727 | h9727
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h9728 | h9728
                            · linarith only [h0, h6793, h9711, h9712, h9725, h9728, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h6793, h9711, h9712, h9728, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h6793, h9711, h9712, h9727, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h6793, h9706, h9711, h9724, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h9434, h9711, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h6793, h9435, h9709, h9710, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9735 | h9735
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9736 | h9736
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9737 | h9737
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9738 | h9738
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9739 | h9739
                        · linarith only [h0, h6793, h9435, h9737, h9739, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9741 | h9741
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h9742 | h9742
                            · linarith only [h0, h6793, h9433, h9435, h9736, h9737, h9739, h9742, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h9744 | h9744
                              · linarith only [h0, h6793, h9435, h9709, h9736, h9737, h9744, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h9746 | h9746
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h9747 | h9747
                                  · rcases h0bigk with h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c | h9748c
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [hlam, p9748_0]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h0, hlam, p9748_1]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h0, h9435, h9737, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9748_1]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h6794, hlam, p9748_1]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h0, h9435, h9737, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p9748_1]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h9435, h9737, hc01, hc12, hlam, hphi, p9748_1]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [hlam, p9748_0]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h6793, h9435, h9737, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9748_1]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h9435, hlam, p9748_1]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h9433, h9435, h9737, h9738, h9744, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9748_1]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h6793, hlam, p9748_1]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h9434, hlam, p9748_1]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [hlam, p9748_0]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h9707, hlam, p9748_1]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h9709, hlam, p9748_1]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h9433, h9738, h9744, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9748_1, u0elo3]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h0, h9433, h9435, h9737, h9738, h9744, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9748_1]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      rcases p9748_3 (m.d 0 1) (by simp) with h9766 | h9766
                                      · linarith only [h6794, h9766, hlam]
                                      · linarith only [h6793, h9766, hlam]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [hlam, p9748_0]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      rcases p9748_3 (m.d 0 1) (by simp) with h9770 | h9770
                                      · linarith only [h6794, h9770, hlam]
                                      · linarith only [h9433, h9770, hlam]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h9433, hlam, p9748_0]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h9706, hlam, p9748_1]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h6793, h6794, h9433, h9736, h9739, hc23, hc34, hlam, hphi, p9748_1]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [h9735, hlam, p9748_1]
                                    · have p9748_0 := h9748c.1
                                      have p9748_1 := h9748c.2.1
                                      have p9748_2 := h9748c.2.2.1
                                      have p9748_3 := h9748c.2.2.2
                                      linarith only [hlam, p9748_0]
                                  · linarith only [h6793, h6794, h9736, h9739, h9747, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h0, h9433, h9435, h9738, h9744, h9746, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h9433, h9435, h9735, h9737, h9741, hlam]
                      · linarith only [h9435, h9706, h9738, hc12, hc24, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9782 | h9782
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9783 | h9783
                        · linarith only [h0, h6793, h9737, h9783, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9785 | h9785
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h9786 | h9786
                            · linarith only [h0, h6793, h9736, h9737, h9783, h9786, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h6793, h9736, h9737, h9786, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h6793, h9736, h9737, h9785, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h6793, h9706, h9736, h9782, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h9434, h9736, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h9433, h9435, h9735, hlam]
          · linarith only [h0, h9433, h9706, hlam]
      · linarith only [h0, h6793, h9434, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h9795 | h9795
      · rcases m.htr 0 2 4 (by decide) (by decide) with h9796 | h9796
        · rcases m.htr 0 2 5 (by decide) (by decide) with h9797 | h9797
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9798 | h9798
            · linarith only [h6793, h6794, h9798, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9800 | h9800
              · linarith only [h6793, h9433, h9800, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9802 | h9802
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9803 | h9803
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9804 | h9804
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9805 | h9805
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9806 | h9806
                        · linarith only [h6793, h6794, h9798, h9806, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9808 | h9808
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h9809 | h9809
                            · linarith only [h6793, h9433, h9803, h9806, h9808, h9809, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h9811 | h9811
                              · linarith only [h6793, h9800, h9803, h9811, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h9813 | h9813
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h9814 | h9814
                                  · rcases h0bigk with h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c | h9815c
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [hlam, p9815_0]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [h0, hlam, p9815_1]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [h9433, h9806, h9808, hc03, hc34, hlam, hphi, p9815_1]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [h6794, hlam, p9815_1]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [h9433, hlam, p9815_1]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [h6793, h9803, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9815_1, u0elo1]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [hlam, p9815_0]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      rcases p9815_3 (m.d 0 1) (by simp) with h9823 | h9823
                                      · linarith only [h0, h9823, hlam]
                                      · linarith only [h6793, h9823, hlam]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [h6793, h6794, h9803, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9815_1, u0elo1]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [h6793, h9433, h9803, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9815_1, u0elo1]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [h6793, hlam, p9815_1]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [h9795, hlam, p9815_1]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [hlam, p9815_0]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [h9798, hlam, p9815_1]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [h9800, hlam, p9815_1]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [h6793, h9803, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9815_1, u0elo3]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [h9796, hlam, p9815_0]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      rcases p9815_3 (m.d 0 1) (by simp) with h9835 | h9835
                                      · linarith only [h6794, h9835, hlam]
                                      · linarith only [h6793, h9835, hlam]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [hlam, p9815_0]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [h6793, h9433, h9796, h9803, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9815_1, u0elo1]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [h6793, h9803, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9815_1, u0elo4]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [h9797, hlam, p9815_1]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      rcases p9815_3 (m.d 0 1) (by simp) with h9842 | h9842
                                      · linarith only [h9433, h9842, hlam]
                                      · linarith only [h6793, h9842, hlam]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [h9802, hlam, p9815_1]
                                    · have p9815_0 := h9815c.1
                                      have p9815_1 := h9815c.2.1
                                      have p9815_2 := h9815c.2.2.1
                                      have p9815_3 := h9815c.2.2.2
                                      linarith only [hlam, p9815_0]
                                  · linarith only [h9796, h9806, h9813, h9814, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h9848 | h9848
                                  · rcases h0bigk with h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c | h9849c
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [hlam, p9849_0]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [h0, hlam, p9849_1]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [h6793, h6794, h9803, h9806, hc23, hc34, hlam, hphi, p9849_1]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [h6794, hlam, p9849_1]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [h9433, hlam, p9849_1]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [h6793, h9803, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9849_1, u0elo1]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [hlam, p9849_0]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      rcases p9849_3 (m.d 0 1) (by simp) with h9857 | h9857
                                      · linarith only [h0, h9857, hlam]
                                      · linarith only [h6793, h9857, hlam]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [h9802, h9813, hc24, hlam, hphi, ht0b, ht45, ht5b, p9849_1, u0elo1]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [h6793, h9433, h9803, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9849_1, u0elo1]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [h6793, hlam, p9849_1]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [h9795, hlam, p9849_1]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [hlam, p9849_0]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [h9798, hlam, p9849_1]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [h9800, hlam, p9849_1]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [h6793, h9803, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9849_1, u0elo3]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [h9796, hlam, p9849_0]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      rcases p9849_3 (m.d 0 1) (by simp) with h9869 | h9869
                                      · linarith only [h6794, h9869, hlam]
                                      · linarith only [h6793, h9869, hlam]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [hlam, p9849_0]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [h6793, h9433, h9796, h9803, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9849_1, u0elo1]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [h6793, h9803, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9849_1, u0elo4]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [h9797, hlam, p9849_1]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      rcases p9849_3 (m.d 0 1) (by simp) with h9876 | h9876
                                      · linarith only [h9433, h9876, hlam]
                                      · linarith only [h6793, h9876, hlam]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [h9802, hlam, p9849_1]
                                    · have p9849_0 := h9849c.1
                                      have p9849_1 := h9849c.2.1
                                      have p9849_2 := h9849c.2.2.1
                                      have p9849_3 := h9849c.2.2.2
                                      linarith only [hlam, p9849_0]
                                  · linarith only [h6793, h6794, h9803, h9806, h9848, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h6794, h9802, h9808, hlam]
                      · linarith only [h0, h6793, h9797, h9803, h9805, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h9796, h9804, hlam]
                  · linarith only [h0, h9795, h9803, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9886 | h9886
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9887 | h9887
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9888 | h9888
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9889 | h9889
                        · linarith only [h6793, h6794, h9802, h9889, hc34, hc45, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9891 | h9891
                          · linarith only [h6793, h6794, h9802, h9889, h9891, hc13, hc34, hlam, hphi]
                          · linarith only [h6793, h6794, h9886, h9891, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h6793, h9797, h9886, h9888, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h6793, h9796, h9886, h9887, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h9795, h9886, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9897 | h9897
            · linarith only [h6793, h6794, h9897, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9899 | h9899
              · linarith only [h0, h6793, h9797, h9899, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9901 | h9901
                · linarith only [h9796, h9797, h9901, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9903 | h9903
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9904 | h9904
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9905 | h9905
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9906 | h9906
                        · linarith only [h6793, h9897, h9906, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9908 | h9908
                          · linarith only [h6793, h6794, h9901, h9903, h9906, h9908, hc23, hc34, hlam, hphi]
                          · linarith only [h6793, h6794, h9903, h9908, hc23, hc45, hlam, hphi, ht34]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9911 | h9911
                        · linarith only [h0, h6793, h9905, h9911, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9913 | h9913
                          · linarith only [h6794, h9901, h9904, h9905, h9913, hc01, hc25, hlam, hphi, ht12]
                          · linarith only [h6793, h6794, h9903, h9913, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6793, h9796, h9903, h9904, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h9795, h9903, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h9918 | h9918
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9919 | h9919
            · linarith only [h0, h6793, h9796, h9919, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9921 | h9921
              · linarith only [h6793, h9433, h9921, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9923 | h9923
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9924 | h9924
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9925 | h9925
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9926 | h9926
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9927 | h9927
                        · linarith only [h6793, h9433, h9796, h9918, h9919, h9925, h9927, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9929 | h9929
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h9930 | h9930
                            · linarith only [h6793, h9796, h9918, h9924, h9925, h9927, h9930, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h9932 | h9932
                              · linarith only [h6793, h9433, h9796, h9918, h9921, h9924, h9925, h9932, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h9934 | h9934
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h9935 | h9935
                                  · rcases h0bigk with h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c | h9936c
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [hlam, p9936_0]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h0, hlam, p9936_1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h9433, h9796, h9918, h9925, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9936_1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h6794, hlam, p9936_1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h9433, hlam, p9936_1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h9796, h9925, hc01, hc12, hlam, hphi, p9936_1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [hlam, p9936_0]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h6793, h9796, h9924, h9925, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9936_1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h9796, hlam, p9936_1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h9796, h9925, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p9936_1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h6793, hlam, p9936_1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h9795, hlam, p9936_1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [hlam, p9936_0]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h9919, hlam, p9936_1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h9921, hlam, p9936_1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h6793, h9924, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9936_1, u0elo3]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h9796, h9918, h9925, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p9936_1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      rcases p9936_3 (m.d 0 1) (by simp) with h9954 | h9954
                                      · linarith only [h6794, h9954, hlam]
                                      · linarith only [h6793, h9954, hlam]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [hlam, p9936_0]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h6793, h9433, h9796, h9924, h9925, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9936_1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h6793, h9918, h9924, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9936_1, u0elo1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h9918, hlam, p9936_1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h6793, h9796, h9918, h9924, h9925, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9936_1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [h9923, hlam, p9936_1]
                                    · have p9936_0 := h9936c.1
                                      have p9936_1 := h9936c.2.1
                                      have p9936_2 := h9936c.2.2.1
                                      have p9936_3 := h9936c.2.2.2
                                      linarith only [hlam, p9936_0]
                                  · linarith only [h0, h6793, h9796, h9924, h9925, h9927, h9935, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h9796, h9918, h9923, h9934, hlam]
                          · linarith only [h9796, h9918, h9923, h9925, h9929, hlam]
                      · linarith only [h9796, h9918, h9926, hc12, hc24, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9968 | h9968
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9969 | h9969
                        · linarith only [h6793, h9433, h9925, h9968, h9969, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9971 | h9971
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h9972 | h9972
                            · linarith only [h6793, h6794, h9433, h9924, h9925, h9968, h9969, h9972, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h6793, h9433, h9924, h9925, h9968, h9972, hc23, hc34, hlam, hphi]
                          · linarith only [h6793, h6794, h9924, h9971, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h9918, h9968, hlam]
                  · linarith only [h0, h9795, h9924, hlam]
                · linarith only [h9796, h9918, h9923, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9979 | h9979
            · linarith only [h0, h6793, h9796, h9979, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9981 | h9981
              · linarith only [h0, h6793, h9918, h9981, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9983 | h9983
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9984 | h9984
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9985 | h9985
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9986 | h9986
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9987 | h9987
                        · linarith only [h0, h6793, h9796, h9979, h9985, h9987, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9989 | h9989
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h9990 | h9990
                            · linarith only [h0, h6793, h9918, h9984, h9986, h9987, h9989, h9990, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h9992 | h9992
                              · linarith only [h0, h6793, h9796, h9981, h9984, h9985, h9992, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h9994 | h9994
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h9995 | h9995
                                  · rcases h0bigk with h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c | h9996c
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [hlam, p9996_0]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h0, hlam, p9996_1]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h0, h9918, h9985, h9994, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9996_1]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h6794, hlam, p9996_1]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h9433, hlam, p9996_1]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h9918, h9985, h9994, hc01, hc12, hlam, hphi, p9996_1]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [hlam, p9996_0]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h6793, h9918, h9984, h9985, h9994, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9996_1]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h9796, hlam, p9996_1]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h9918, hlam, p9996_0]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h6793, hlam, p9996_1]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h9795, hlam, p9996_1]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [hlam, p9996_0]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h9979, hlam, p9996_1]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h9981, hlam, p9996_1]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h6793, h9984, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9996_1, u0elo3]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h0, h6793, h9796, h9984, h9985, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9996_1]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      rcases p9996_3 (m.d 0 1) (by simp) with h10014 | h10014
                                      · linarith only [h10014, h6794, hlam]
                                      · linarith only [h10014, h6793, hlam]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [hlam, p9996_0]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h0, h6793, h9796, h9918, h9984, h9985, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9996_1]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h6793, h9984, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9996_1, u0elo4]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h0, h6793, h9918, h9984, h9985, h9994, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9996_1]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      rcases p9996_3 (m.d 0 1) (by simp) with h10021 | h10021
                                      · linarith only [h10021, h9433, hlam]
                                      · linarith only [h10021, h6793, hlam]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [h9983, hlam, p9996_1]
                                    · have p9996_0 := h9996c.1
                                      have p9996_1 := h9996c.2.1
                                      have p9996_2 := h9996c.2.2.1
                                      have p9996_3 := h9996c.2.2.2
                                      linarith only [hlam, p9996_0]
                                  · linarith only [h6793, h6794, h9984, h9987, h9995, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h9796, h9983, h9994, hlam]
                          · linarith only [h6793, h6794, h9983, h9984, h9989, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h0, h6793, h9796, h9984, h9985, h9986, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10030 | h10030
                      · linarith only [h0, h10030, h6793, h9918, h9984, h9985, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h10032 | h10032
                        · linarith only [h0, h10032, h6793, h9979, h9985, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h10034 | h10034
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h10035 | h10035
                            · linarith only [h0, h10030, h10032, h10034, h10035, h6793, h9984, hlam]
                            · linarith only [h0, h10035, h6793, h9984, h9985, hc23, hc34, hlam, hphi]
                          · linarith only [h10034, h6794, h9983, hlam]
                  · linarith only [h0, h9795, h9984, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h10040 | h10040
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h10041 | h10041
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10042 | h10042
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h10043 | h10043
                        · linarith only [h0, h10041, h10043, h6793, h9796, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h10045 | h10045
                          · linarith only [h10043, h10045, h6793, h6794, h9983, hc13, hc34, hlam, hphi]
                          · linarith only [h10040, h10045, h6793, h6794, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h10041, h10042, h9796, hc02, hc25, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10049 | h10049
                      · linarith only [h0, h10040, h10041, h10049, h6793, h9918, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h10051 | h10051
                        · linarith only [h0, h10041, h10051, h6793, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h10053 | h10053
                          · linarith only [h10040, h10051, h10053, h6793, h6794, h9983, hc23, hc34, hlam, hphi]
                          · linarith only [h10040, h10053, h6793, h6794, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h10040, h9795, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · linarith only [h0, h6793, h9795, hlam]

end R2N4
