import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_39S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h478 | h478
  · rcases m.htr 1 2 4 (by decide) (by decide) with h479 | h479
    · rcases m.htr 1 2 5 (by decide) (by decide) with h480 | h480
      · rcases m.htr 1 3 4 (by decide) (by decide) with h481 | h481
        · rcases m.htr 1 3 5 (by decide) (by decide) with h482 | h482
          · rcases m.htr 1 4 5 (by decide) (by decide) with h483 | h483
            · linarith only [h2, h483, h7, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h485 | h485
              · rcases m.htr 2 3 5 (by decide) (by decide) with h486 | h486
                · rcases m.htr 2 4 5 (by decide) (by decide) with h487 | h487
                  · linarith only [h2, h479, h487, h7, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h489 | h489
                    · linarith only [h478, h485, h489, h7, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases h1bigk with h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c | h491c
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        linarith only [hlam, p491_0]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        linarith only [h478, h485, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p491_1]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        rcases p491_3 (m.d 0 1) (by simp) with h494 | h494
                        · rcases p491_3 (m.d 1 2) (by simp) with h495 | h495
                          · linarith only [h0, h495, hlam]
                          · linarith only [h478, h495, hlam]
                        · linarith only [h494, hlam, p491_0]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        rcases p491_3 (m.d 0 1) (by simp) with h499 | h499
                        · rcases p491_3 (m.d 1 2) (by simp) with h500 | h500
                          · linarith only [h0, h500, hlam]
                          · linarith only [h479, h500, hlam]
                        · linarith only [h499, hlam, p491_0]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        rcases p491_3 (m.d 0 1) (by simp) with h504 | h504
                        · rcases p491_3 (m.d 1 2) (by simp) with h505 | h505
                          · linarith only [h0, h505, hlam]
                          · linarith only [h480, h505, hlam]
                        · linarith only [h504, hlam, p491_0]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        linarith only [h0, hlam, p491_0]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        linarith only [hlam, p491_0]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        linarith only [h0, h478, h486, h489, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p491_1]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        rcases p491_3 (m.d 0 1) (by simp) with h512 | h512
                        · rcases p491_3 (m.d 1 2) (by simp) with h513 | h513
                          · rcases p491_3 (m.d 1 3) (by simp) with h514 | h514
                            · linarith only [h478, h514, hlam]
                            · linarith only [h481, h514, hlam]
                          · linarith only [h479, h513, hlam]
                        · linarith only [h2, h512, hlam]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        rcases p491_3 (m.d 0 1) (by simp) with h519 | h519
                        · rcases p491_3 (m.d 1 2) (by simp) with h520 | h520
                          · rcases p491_3 (m.d 1 3) (by simp) with h521 | h521
                            · linarith only [h478, h521, hlam]
                            · linarith only [h482, h521, hlam]
                          · linarith only [h480, h520, hlam]
                        · linarith only [h3, h519, hlam]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        linarith only [h1, hlam, p491_0]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        linarith only [h478, hlam, p491_1]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        linarith only [hlam, p491_0]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        rcases p491_3 (m.d 0 1) (by simp) with h529 | h529
                        · rcases p491_3 (m.d 1 2) (by simp) with h530 | h530
                          · rcases p491_3 (m.d 1 3) (by simp) with h531 | h531
                            · rcases p491_3 (m.d 1 4) (by simp) with h532 | h532
                              · linarith only [h481, h532, hlam]
                              · rcases p491_3 (m.d 1 5) (by simp) with h534 | h534
                                · linarith only [h482, h534, hlam]
                                · linarith only [h483, h534, hlam]
                            · linarith only [h481, h531, hlam]
                          · linarith only [h479, h530, hlam]
                        · linarith only [h2, h529, hlam]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        rcases p491_3 (m.d 0 1) (by simp) with h540 | h540
                        · rcases p491_3 (m.d 1 2) (by simp) with h541 | h541
                          · rcases p491_3 (m.d 1 3) (by simp) with h542 | h542
                            · rcases p491_3 (m.d 1 4) (by simp) with h543 | h543
                              · linarith only [h481, h543, hlam]
                              · rcases p491_3 (m.d 1 5) (by simp) with h545 | h545
                                · linarith only [h482, h545, hlam]
                                · rcases h1emin with h547 | h547 | h547 | h547 | h547
                                  · rcases h5bigk with h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [hlam, p548_0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h480, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p548_1, u3elo0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p548_1, u3elo0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h489, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p548_1, u3elo0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h7, hlam, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h3, hlam, p548_0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [hlam, p548_0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h3, hc01, hc25, hlam, hphi, ht0b, ht5b, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h489, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p491_1, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h483, hlam, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h4, hlam, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h480, hlam, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [hlam, p548_0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h0, h4, h489, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h487, hlam, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h6, hlam, p548_0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h482, hlam, p548_0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h486, hlam, p548_0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [hlam, p548_0]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h489, hlam, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h489, h6, hc34, hc45, hlam, hphi, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h482, h489, hc34, hc45, hlam, hphi, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h486, h489, hc34, hc45, hlam, hphi, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [h489, hc34, hc45, hlam, hphi, p548_1]
                                    · have p548_0 := h548c.1
                                      have p548_1 := h548c.2.1
                                      have p548_2 := h548c.2.2.1
                                      have p548_3 := h548c.2.2.2
                                      linarith only [hlam, p548_0]
                                  · rcases h5bigk with h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h479, h483, h485, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p574_1, u3elo0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h486, h489, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p574_1, u3elo0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h489, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p574_1, u3elo0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h7, hlam, p574_1]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h3, hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h3, h486, h489, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h1, h489, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p491_1, p574_1, u3elo0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h483, hlam, p574_1]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h4, hlam, p574_1]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h480, hlam, p574_1]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h0, h4, h489, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h487, hlam, p574_1]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h6, hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h482, hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h486, hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [hlam, p574_0]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h489, hlam, p574_1]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h489, h6, hc34, hc45, hlam, hphi, p574_1]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h482, h489, hc34, hc45, hlam, hphi, p574_1]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h486, h489, hc34, hc45, hlam, hphi, p574_1]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [h489, hc34, hc45, hlam, hphi, p574_1]
                                    · have p574_0 := h574c.1
                                      have p574_1 := h574c.2.1
                                      have p574_2 := h574c.2.2.1
                                      have p574_3 := h574c.2.2.2
                                      linarith only [hlam, p574_0]
                                  · linarith only [h1, h547, hlam, ht12, ht23, u3elo0]
                                  · linarith only [h2, h5, h547, hlam, ht12, ht23, u3elo0]
                                  · linarith only [h3, h547, h6, hlam, ht12, ht23, u3elo0]
                            · linarith only [h482, h542, hlam]
                          · linarith only [h480, h541, hlam]
                        · linarith only [h3, h540, hlam]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        linarith only [h2, hlam, p491_0]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        linarith only [h479, hlam, p491_1]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        linarith only [h481, hlam, p491_0]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        linarith only [hlam, p491_0]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        linarith only [h483, hlam, p491_1]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        linarith only [h3, hlam, p491_0]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        linarith only [h480, hlam, p491_1]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        linarith only [h482, hlam, p491_0]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        rcases p491_3 (m.d 0 1) (by simp) with h614 | h614
                        · rcases p491_3 (m.d 1 2) (by simp) with h615 | h615
                          · rcases p491_3 (m.d 1 3) (by simp) with h616 | h616
                            · rcases p491_3 (m.d 1 4) (by simp) with h617 | h617
                              · linarith only [h483, h617, hlam]
                              · rcases p491_3 (m.d 1 5) (by simp) with h619 | h619
                                · rcases h1emin with h620 | h620 | h620 | h620 | h620
                                  · rcases h5bigk with h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [hlam, p621_0]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h479, h485, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p491_1, p621_1, u3elo0]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p621_1, u3elo0]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p621_1, u3elo0]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h7, hlam, p621_1]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h3, hlam, p621_0]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [hlam, p621_0]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h0, h478, h482, hc01, hc25, hlam, hphi, ht0b, ht5b, p621_1]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h1, h482, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p621_1, u3elo0]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h483, hlam, p621_1]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h4, hlam, p621_1]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h480, hlam, p621_1]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [hlam, p621_0]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h0, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p621_1]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h487, hlam, p621_1]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h6, hlam, p621_0]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h482, hlam, p621_0]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h486, hlam, p621_0]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [hlam, p621_0]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h489, hlam, p621_1]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h7, hc04, hc45, hlam, hphi, p621_1]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h479, h485, hc34, hc45, hlam, hphi, p491_1, p621_1]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h485, h487, hc34, hc45, hlam, hphi, p621_1]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [h489, hc34, hc45, hlam, hphi, p621_1]
                                    · have p621_0 := h621c.1
                                      have p621_1 := h621c.2.1
                                      have p621_2 := h621c.2.2.1
                                      have p621_3 := h621c.2.2.2
                                      linarith only [hlam, p621_0]
                                  · rcases h5bigk with h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [hlam, p647_0]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h479, h485, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p491_1, p647_1]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h485, h487, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p647_1, u3elo0]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h489, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p647_1, u3elo0]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h7, hlam, p647_1]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h3, hlam, p647_0]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [hlam, p647_0]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h3, h485, h487, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p647_1]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h3, h489, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p647_1, u3elo0]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h483, hlam, p647_1]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h4, hlam, p647_1]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h480, hlam, p647_1]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [hlam, p647_0]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h0, h4, h489, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p647_1]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h487, hlam, p647_1]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h6, hlam, p647_0]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h482, hlam, p647_0]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h486, hlam, p647_0]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [hlam, p647_0]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h489, hlam, p647_1]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h489, h6, hc34, hc45, hlam, hphi, p647_1]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h482, h489, hc34, hc45, hlam, hphi, p647_1]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h486, h489, hc34, hc45, hlam, hphi, p647_1]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [h489, hc34, hc45, hlam, hphi, p647_1]
                                    · have p647_0 := h647c.1
                                      have p647_1 := h647c.2.1
                                      have p647_2 := h647c.2.2.1
                                      have p647_3 := h647c.2.2.2
                                      linarith only [hlam, p647_0]
                                  · linarith only [h1, h620, hlam, ht12, ht23, u3elo0]
                                  · linarith only [h3, h620, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p491_1]
                                  · linarith only [h3, h6, h620, hlam, ht12, ht23, u3elo0]
                                · linarith only [h483, h619, hlam]
                            · linarith only [h481, h616, hlam]
                          · linarith only [h479, h615, hlam]
                        · linarith only [h2, h614, hlam]
                      · have p491_0 := h491c.1
                        have p491_1 := h491c.2.1
                        have p491_2 := h491c.2.2.1
                        have p491_3 := h491c.2.2.2
                        linarith only [hlam, p491_0]
                · linarith only [h486, h6, hc23, hlam, hphi, u3elo0]
              · linarith only [h485, h5, hc23, hlam, hphi, u3elo0]
          · linarith only [h482, h6, hc13, hlam, hphi, u3elo0]
        · linarith only [h478, h481, h5, hc23, hlam, hphi, u3elo0]
      · linarith only [h4, h478, h480, h6, hc23, hlam, hphi, u3elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h686 | h686
      · rcases m.htr 1 3 4 (by decide) (by decide) with h687 | h687
        · linarith only [h478, h479, h687, hlam]
        · linarith only [h5, h687, hc13, hlam, hphi, u3elo0]
      · linarith only [h4, h478, h6, h686, hc23, hlam, hphi, u3elo0]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h691 | h691
    · rcases m.htr 1 2 5 (by decide) (by decide) with h692 | h692
      · rcases m.htr 1 3 4 (by decide) (by decide) with h693 | h693
        · rcases m.htr 1 3 5 (by decide) (by decide) with h694 | h694
          · rcases m.htr 1 4 5 (by decide) (by decide) with h695 | h695
            · linarith only [h2, h695, h7, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h697 | h697
              · rcases m.htr 2 3 5 (by decide) (by decide) with h698 | h698
                · rcases m.htr 2 4 5 (by decide) (by decide) with h699 | h699
                  · linarith only [h478, h691, h699, h7, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h701 | h701
                    · linarith only [h5, h7, h701, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                    · rcases h1bigk with h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c | h703c
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [hlam, p703_0]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        rcases p703_3 (m.d 0 1) (by simp) with h705 | h705
                        · rcases p703_3 (m.d 1 2) (by simp) with h706 | h706
                          · linarith only [h706, hlam, p703_0]
                          · rcases p703_3 (m.d 1 3) (by simp) with h708 | h708
                            · linarith only [h1, h708, hlam]
                            · linarith only [h478, h708, hlam]
                        · linarith only [h705, hlam, p703_0]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        rcases p703_3 (m.d 0 1) (by simp) with h712 | h712
                        · rcases p703_3 (m.d 1 2) (by simp) with h713 | h713
                          · linarith only [h0, h713, hlam]
                          · rcases p703_3 (m.d 1 3) (by simp) with h715 | h715
                            · linarith only [h715, hlam, p703_0]
                            · rcases p703_3 (m.d 1 4) (by simp) with h717 | h717
                              · linarith only [h2, h717, hlam]
                              · rcases p703_3 (m.d 1 5) (by simp) with h719 | h719
                                · linarith only [h3, h719, hlam]
                                · rcases h1emin with h721 | h721 | h721 | h721 | h721
                                  · rcases h5bigk with h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [hlam, p722_0]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h6, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p722_1, u3elo0]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h6, h698, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p722_1, u3elo0]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p722_1, u3elo0]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h7, hlam, p722_1]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h3, hlam, p722_0]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [hlam, p722_0]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h3, h698, hc01, hc35, hlam, hphi, ht0b, ht5b, p722_1]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h478, h692, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p722_1, u3elo2]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h695, hlam, p722_1]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h4, hlam, p722_1]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h692, hlam, p722_1]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [hlam, p722_0]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h4, hc02, hc35, hlam, hphi, ht0b, ht5b, p722_1]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h699, hlam, p722_1]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h6, hlam, p722_0]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h694, hlam, p722_0]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h698, hlam, p722_0]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [hlam, p722_0]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h701, hlam, p722_1]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h2, h691, h697, h7, hc34, hc45, hlam, hphi, p722_1]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h691, h695, h697, hc34, hc45, hlam, hphi, p722_1]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h697, h699, hc34, hc45, hlam, hphi, p722_1]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [h701, hc34, hc45, hlam, hphi, p722_1]
                                    · have p722_0 := h722c.1
                                      have p722_1 := h722c.2.1
                                      have p722_2 := h722c.2.2.1
                                      have p722_3 := h722c.2.2.2
                                      linarith only [hlam, p722_0]
                                  · linarith only [h478, h721, hlam, ht12, ht23, u3elo2]
                                  · linarith only [h721, hlam, ht12, ht23, u3elo1]
                                  · linarith only [h2, h5, h721, hlam, ht12, ht23, u3elo0]
                                  · linarith only [h3, h6, h721, hlam, ht12, ht23, u3elo0]
                        · linarith only [h712, hlam, p703_0]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        rcases p703_3 (m.d 0 1) (by simp) with h753 | h753
                        · rcases p703_3 (m.d 1 2) (by simp) with h754 | h754
                          · linarith only [h0, h754, hlam]
                          · linarith only [h691, h754, hlam]
                        · linarith only [h753, hlam, p703_0]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        rcases p703_3 (m.d 0 1) (by simp) with h758 | h758
                        · rcases p703_3 (m.d 1 2) (by simp) with h759 | h759
                          · linarith only [h0, h759, hlam]
                          · linarith only [h692, h759, hlam]
                        · linarith only [h758, hlam, p703_0]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [h0, hlam, p703_0]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [hlam, p703_0]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [h478, hlam, p703_0]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [h478, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p703_1, u3elo2]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [h478, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p703_1, u3elo2]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [h1, hlam, p703_0]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht23, p703_1, u3elo0]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [hlam, p703_0]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        rcases p703_3 (m.d 0 1) (by simp) with h771 | h771
                        · rcases p703_3 (m.d 1 2) (by simp) with h772 | h772
                          · linarith only [h478, h772, hlam]
                          · linarith only [h691, h772, hlam]
                        · linarith only [h2, h771, hlam]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        rcases p703_3 (m.d 0 1) (by simp) with h776 | h776
                        · rcases p703_3 (m.d 1 2) (by simp) with h777 | h777
                          · linarith only [h478, h777, hlam]
                          · linarith only [h692, h777, hlam]
                        · linarith only [h3, h776, hlam]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [h2, hlam, p703_0]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [h691, hlam, p703_1]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [h693, hlam, p703_0]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [hlam, p703_0]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [h695, hlam, p703_1]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [h3, hlam, p703_0]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [h692, hlam, p703_1]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [h694, hlam, p703_0]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [h478, h691, h692, h697, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p703_1, u3elo2]
                      · have p703_0 := h703c.1
                        have p703_1 := h703c.2.1
                        have p703_2 := h703c.2.2.1
                        have p703_3 := h703c.2.2.2
                        linarith only [hlam, p703_0]
                · linarith only [h478, h698, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h478, h5, h697, hc13, hlam, hphi, u3elo0]
          · linarith only [h478, h6, h691, h694, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
        · linarith only [h478, h5, h691, h693, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h795 | h795
        · rcases m.htr 1 3 5 (by decide) (by decide) with h796 | h796
          · rcases m.htr 1 4 5 (by decide) (by decide) with h797 | h797
            · linarith only [h2, h7, h797, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h799 | h799
              · rcases m.htr 2 3 5 (by decide) (by decide) with h800 | h800
                · rcases m.htr 2 4 5 (by decide) (by decide) with h801 | h801
                  · linarith only [h0, h4, h691, h692, h7, h801, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h803 | h803
                    · linarith only [h4, h692, h7, h803, hc12, hlam, hphi, ht23, u3elo3]
                    · rcases h1bigk with h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [hlam, p805_0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        rcases p805_3 (m.d 0 1) (by simp) with h807 | h807
                        · rcases p805_3 (m.d 1 2) (by simp) with h808 | h808
                          · linarith only [h808, hlam, p805_0]
                          · rcases p805_3 (m.d 1 3) (by simp) with h810 | h810
                            · linarith only [h1, h810, hlam]
                            · linarith only [h478, h810, hlam]
                        · linarith only [h807, hlam, p805_0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        rcases p805_3 (m.d 0 1) (by simp) with h814 | h814
                        · rcases p805_3 (m.d 1 2) (by simp) with h815 | h815
                          · linarith only [h0, h815, hlam]
                          · rcases p805_3 (m.d 1 3) (by simp) with h817 | h817
                            · linarith only [h817, hlam, p805_0]
                            · rcases p805_3 (m.d 1 4) (by simp) with h819 | h819
                              · linarith only [h2, h819, hlam]
                              · rcases p805_3 (m.d 1 5) (by simp) with h821 | h821
                                · linarith only [h3, h821, hlam]
                                · rcases h1emin with h823 | h823 | h823 | h823 | h823
                                  · rcases h5bigk with h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c | h824c
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [hlam, p824_0]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h691, h692, h799, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p824_1]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h691, h692, h7, h799, hc34, hc45, hlam, hphi, p824_1]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h6, h803, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p824_1, u3elo0]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h7, hlam, p824_1]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h3, hlam, p824_0]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [hlam, p824_0]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h692, hlam, p824_0]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h796, h803, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p805_1, p824_1]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h797, hlam, p824_1]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h4, hlam, p824_1]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h4, hc02, hc15, hlam, hphi, ht0b, ht5b, p824_1]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [hlam, p824_0]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h4, h6, h803, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p824_1, u3elo0]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h801, hlam, p824_1]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h6, hlam, p824_0]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h796, hlam, p824_0]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h800, hlam, p824_0]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [hlam, p824_0]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h803, hlam, p824_1]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h3, h691, h692, h799, hc34, hc45, hlam, hphi, p824_1]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h691, h692, h799, hc34, hc45, hlam, hphi, p824_1]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h691, h692, h799, hc34, hc45, hlam, hphi, p824_1]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [h803, hc34, hc45, hlam, hphi, p824_1]
                                    · have p824_0 := h824c.1
                                      have p824_1 := h824c.2.1
                                      have p824_2 := h824c.2.2.1
                                      have p824_3 := h824c.2.2.2
                                      linarith only [hlam, p824_0]
                                  · linarith only [h692, h823, hc25, hlam, ht12]
                                  · linarith only [h823, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p805_1]
                                  · linarith only [h2, h5, h823, hlam, ht12, ht23, u3elo0]
                                  · linarith only [h3, h6, h823, hlam, ht12, ht23, u3elo0]
                        · linarith only [h814, hlam, p805_0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        rcases p805_3 (m.d 0 1) (by simp) with h855 | h855
                        · rcases p805_3 (m.d 1 2) (by simp) with h856 | h856
                          · linarith only [h0, h856, hlam]
                          · linarith only [h691, h856, hlam]
                        · linarith only [h855, hlam, p805_0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        rcases p805_3 (m.d 0 1) (by simp) with h860 | h860
                        · rcases p805_3 (m.d 1 2) (by simp) with h861 | h861
                          · linarith only [h0, h861, hlam]
                          · rcases p805_3 (m.d 1 3) (by simp) with h863 | h863
                            · linarith only [h1, h863, hlam]
                            · linarith only [h796, h863, hlam]
                        · linarith only [h860, hlam, p805_0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [h0, hlam, p805_0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [hlam, p805_0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [h478, hlam, p805_0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [h4, h6, h692, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p805_1, u3elo0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [h692, hlam, p805_0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [h1, hlam, p805_0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [hc12, hlam, hphi, ht23, p805_1, u3elo1]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [hlam, p805_0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        rcases p805_3 (m.d 0 1) (by simp) with h875 | h875
                        · rcases p805_3 (m.d 1 2) (by simp) with h876 | h876
                          · linarith only [h478, h876, hlam]
                          · linarith only [h691, h876, hlam]
                        · linarith only [h2, h875, hlam]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [h1, h691, h692, h799, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p805_1, u3elo0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [h2, hlam, p805_0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [h691, hlam, p805_1]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [h795, hlam, p805_0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [hlam, p805_0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [h797, hlam, p805_1]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [h3, hlam, p805_0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [h3, h691, h799, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p805_1]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [h796, hlam, p805_0]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        rcases p805_3 (m.d 0 1) (by simp) with h889 | h889
                        · rcases p805_3 (m.d 1 2) (by simp) with h890 | h890
                          · linarith only [h692, h890, hlam]
                          · linarith only [h691, h890, hlam]
                        · linarith only [h2, h889, hlam]
                      · have p805_0 := h805c.1
                        have p805_1 := h805c.2.1
                        have p805_2 := h805c.2.2.1
                        have p805_3 := h805c.2.2.2
                        linarith only [hlam, p805_0]
                · linarith only [h6, h800, hc23, hlam, hphi, u3elo0]
              · linarith only [h478, h5, h799, hc13, hlam, hphi, u3elo0]
          · linarith only [h478, h6, h796, hc12, hlam, hphi, ht23, u3elo0]
        · linarith only [h478, h5, h691, h795, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h899 | h899
      · rcases m.htr 1 3 4 (by decide) (by decide) with h900 | h900
        · rcases m.htr 1 3 5 (by decide) (by decide) with h901 | h901
          · rcases m.htr 1 4 5 (by decide) (by decide) with h902 | h902
            · linarith only [h2, h7, h902, hlam]
            · linarith only [h691, h899, h902, hlam]
          · linarith only [h6, h691, h900, h901, hc12, hlam, hphi, ht23, u3elo0]
        · linarith only [h478, h5, h899, h900, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h907 | h907
        · rcases m.htr 1 3 5 (by decide) (by decide) with h908 | h908
          · rcases m.htr 1 4 5 (by decide) (by decide) with h909 | h909
            · linarith only [h2, h7, h909, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h911 | h911
              · rcases m.htr 2 3 5 (by decide) (by decide) with h912 | h912
                · rcases m.htr 2 4 5 (by decide) (by decide) with h913 | h913
                  · linarith only [h4, h7, h899, h911, h913, hc12, hlam, hphi, ht23, u3elo2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h915 | h915
                    · linarith only [h691, h907, h913, h915, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases h1bigk with h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [hlam, p917_0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        rcases p917_3 (m.d 0 1) (by simp) with h919 | h919
                        · rcases p917_3 (m.d 1 2) (by simp) with h920 | h920
                          · linarith only [h920, hlam, p917_0]
                          · rcases p917_3 (m.d 1 3) (by simp) with h922 | h922
                            · linarith only [h1, h922, hlam]
                            · linarith only [h478, h922, hlam]
                        · linarith only [h919, hlam, p917_0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        rcases p917_3 (m.d 0 1) (by simp) with h926 | h926
                        · rcases p917_3 (m.d 1 2) (by simp) with h927 | h927
                          · linarith only [h0, h927, hlam]
                          · rcases p917_3 (m.d 1 3) (by simp) with h929 | h929
                            · linarith only [h929, hlam, p917_0]
                            · rcases p917_3 (m.d 1 4) (by simp) with h931 | h931
                              · linarith only [h2, h931, hlam]
                              · rcases p917_3 (m.d 1 5) (by simp) with h933 | h933
                                · linarith only [h3, h933, hlam]
                                · rcases h1emin with h935 | h935 | h935 | h935 | h935
                                  · rcases h5bigk with h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [hlam, p936_0]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h6, h909, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p936_1, u3elo0]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p936_1, u3elo0]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h6, h915, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p936_1, u3elo0]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h7, hlam, p936_1]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h3, hlam, p936_0]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [hlam, p936_0]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h899, hlam, p936_0]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h3, h915, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p936_1]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h909, hlam, p936_1]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h4, hlam, p936_1]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h0, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p936_1]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [hlam, p936_0]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h4, h6, h915, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p936_1, u3elo0]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h913, hlam, p936_1]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h6, hlam, p936_0]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h908, hlam, p936_0]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h912, hlam, p936_0]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [hlam, p936_0]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h915, hlam, p936_1]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h3, h691, h909, hc12, hc45, hlam, hphi, ht23, ht34, p936_1]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h691, h909, hc12, hc45, hlam, hphi, ht23, ht34, p936_1]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h899, hc12, hc45, hlam, hphi, ht23, ht34, p936_1]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [h915, hc34, hc45, hlam, hphi, p936_1]
                                    · have p936_0 := h936c.1
                                      have p936_1 := h936c.2.1
                                      have p936_2 := h936c.2.2.1
                                      have p936_3 := h936c.2.2.2
                                      linarith only [hlam, p936_0]
                                  · linarith only [h691, h935, hc24, hlam, ht12]
                                  · linarith only [h935, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p917_1]
                                  · linarith only [h2, h5, h935, hlam, ht12, ht23, u3elo0]
                                  · linarith only [h3, h6, h935, hlam, ht12, ht23, u3elo0]
                        · linarith only [h926, hlam, p917_0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        rcases p917_3 (m.d 0 1) (by simp) with h967 | h967
                        · rcases p917_3 (m.d 1 2) (by simp) with h968 | h968
                          · linarith only [h0, h968, hlam]
                          · rcases p917_3 (m.d 1 3) (by simp) with h970 | h970
                            · linarith only [h1, h970, hlam]
                            · linarith only [h907, h970, hlam]
                        · linarith only [h967, hlam, p917_0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        rcases p917_3 (m.d 0 1) (by simp) with h974 | h974
                        · rcases p917_3 (m.d 1 2) (by simp) with h975 | h975
                          · linarith only [h0, h975, hlam]
                          · rcases p917_3 (m.d 1 3) (by simp) with h977 | h977
                            · linarith only [h1, h977, hlam]
                            · linarith only [h908, h977, hlam]
                        · linarith only [h974, hlam, p917_0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [h0, hlam, p917_0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [hlam, p917_0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [h478, hlam, p917_0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [h691, hlam, p917_0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [h899, hlam, p917_0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [h1, hlam, p917_0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [hc12, hlam, hphi, ht23, p917_1, u3elo1]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [hlam, p917_0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [h1, h691, hc12, hlam, hphi, ht23, p917_1, u3elo0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [h1, h899, hc12, hlam, hphi, ht23, p917_1, u3elo0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [h2, hlam, p917_0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [h2, h6, h7, hc12, hlam, hphi, ht23, p917_1, u3elo0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [h907, hlam, p917_0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [hlam, p917_0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [h909, hlam, p917_1]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [h3, hlam, p917_0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [h3, h6, hc12, hlam, hphi, ht23, p917_1, u3elo0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [h908, hlam, p917_0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [h4, h6, h691, h899, hc12, hlam, hphi, ht23, p917_1, u3elo0]
                      · have p917_0 := h917c.1
                        have p917_1 := h917c.2.1
                        have p917_2 := h917c.2.2.1
                        have p917_3 := h917c.2.2.2
                        linarith only [hlam, p917_0]
                · linarith only [h6, h912, hc23, hlam, hphi, u3elo0]
              · linarith only [h478, h5, h911, hc13, hlam, hphi, u3elo0]
          · linarith only [h6, h907, h908, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
        · linarith only [h478, h5, h907, hc12, hlam, hphi, ht23, u3elo0]

set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
  · exact r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h5 h6 h7
  · exact r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h5 h6 h7

set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h1005 | h1005
  · linarith only [h1005, h5, h6, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1007 | h1007
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1008 | h1008
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1009 | h1009
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1010 | h1010
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1011 | h1011
            · linarith only [h1011, h6, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1013 | h1013
              · linarith only [h1, h1005, h1010, h1013, h6, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1015 | h1015
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1016 | h1016
                  · linarith only [h1016, h6, hc03, hlam, hphi, u3elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1018 | h1018
                    · linarith only [h1005, h1008, h1018, h2, h5, h6, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1020 | h1020
                      · linarith only [h1005, h1020, h5, h6, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · rcases h1bigk with h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h1007, h1015, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1022_1]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          rcases p1022_3 (m.d 0 1) (by simp) with h1025 | h1025
                          · rcases p1022_3 (m.d 1 2) (by simp) with h1026 | h1026
                            · linarith only [h0, h1026, hlam]
                            · linarith only [h1007, h1026, hlam]
                          · linarith only [h1025, hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          rcases p1022_3 (m.d 0 1) (by simp) with h1030 | h1030
                          · rcases p1022_3 (m.d 1 2) (by simp) with h1031 | h1031
                            · linarith only [h0, h1031, hlam]
                            · linarith only [h1008, h1031, hlam]
                          · linarith only [h1030, hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          rcases p1022_3 (m.d 0 1) (by simp) with h1035 | h1035
                          · rcases p1022_3 (m.d 1 2) (by simp) with h1036 | h1036
                            · linarith only [h0, h1036, hlam]
                            · linarith only [h1009, h1036, hlam]
                          · linarith only [h1035, hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h0, hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h0, h1007, h1015, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1022_1]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          rcases p1022_3 (m.d 0 1) (by simp) with h1043 | h1043
                          · rcases p1022_3 (m.d 1 2) (by simp) with h1044 | h1044
                            · rcases p1022_3 (m.d 1 3) (by simp) with h1045 | h1045
                              · linarith only [h1007, h1045, hlam]
                              · linarith only [h1010, h1045, hlam]
                            · linarith only [h1008, h1044, hlam]
                          · linarith only [h1043, h2, hlam]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h0, h1007, h1011, h1015, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1022_1]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h1, hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h1007, hlam, p1022_1]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h1, h1008, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1022_1, u3elo4]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h1011, hlam, p1022_1]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h2, hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h1008, hlam, p1022_1]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h1010, hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h1013, hlam, p1022_1]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h3, hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h1009, hlam, p1022_1]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h1007, h3, h6, hc23, hlam, hphi, p1022_1, u3elo4]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          rcases p1022_3 (m.d 0 1) (by simp) with h1064 | h1064
                          · rcases p1022_3 (m.d 1 2) (by simp) with h1065 | h1065
                            · rcases p1022_3 (m.d 1 3) (by simp) with h1066 | h1066
                              · linarith only [h1011, h1066, hlam]
                              · linarith only [h1010, h1066, hlam]
                            · linarith only [h1008, h1065, hlam]
                          · linarith only [h1064, h2, hlam]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [hlam, p1022_0]
                · linarith only [h1015, h5, h6, hc23, hlam, hphi, u3elo4]
          · linarith only [h1007, h1010, h5, h6, hc23, hlam, hphi, u3elo4]
        · linarith only [h1007, h1009, h4, h6, hc23, hlam, hphi, u3elo4]
      · linarith only [h1007, h1008, h2, h5, h6, hc23, hlam, hphi, u3elo4]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1076 | h1076
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1077 | h1077
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1078 | h1078
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1079 | h1079
            · linarith only [h1079, h6, hc03, hlam, hphi, u3elo1]
            · linarith only [h1007, h1077, h1079, hlam]
          · linarith only [h1007, h1076, h1078, h5, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1083 | h1083
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1084 | h1084
            · linarith only [h1084, h6, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1086 | h1086
              · linarith only [h1005, h1076, h1077, h1086, h4, h6, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1088 | h1088
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1089 | h1089
                  · linarith only [h1089, h6, hc03, hlam, hphi, u3elo2]
                  · linarith only [h1007, h1076, h1088, h1089, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · linarith only [h1007, h1076, h1088, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
          · linarith only [h1007, h1076, h1083, h5, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1094 | h1094
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1095 | h1095
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1096 | h1096
            · linarith only [h1096, h6, hc03, hlam, hphi, u3elo1]
            · linarith only [h1007, h1094, h1096, hlam]
          · linarith only [h1007, h1094, h1095, h5, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1100 | h1100
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1101 | h1101
            · linarith only [h1101, h6, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1103 | h1103
              · linarith only [h1005, h1100, h1101, h1103, h3, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1105 | h1105
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1106 | h1106
                  · linarith only [h1076, h1106, h2, h5, h6, hc12, hlam, hphi, ht23, u3elo2]
                  · linarith only [h1007, h1106, hc12, hlam, hphi, ht23, u3elo4]
                · linarith only [h1, h1007, h1100, h1105, h6, hc12, hlam, hphi, ht23, u3elo4]
          · linarith only [h1100, h5, h6, hc13, hlam, hphi, u3elo4]

set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h5 h6
  · exact r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h5 h6

end R2N4
