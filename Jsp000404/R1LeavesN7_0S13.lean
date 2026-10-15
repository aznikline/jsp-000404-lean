import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10278000 in
set_option maxHeartbeats 10278000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15_x1_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h4129 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h6948 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h7434 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h7435 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  rcases m.htr 2 3 5 (by decide) (by decide) with h7436 | h7436
  · rcases m.htr 2 4 5 (by decide) (by decide) with h7437 | h7437
    · rcases m.htr 3 4 5 (by decide) (by decide) with h7438 | h7438
      · rcases h1bigk with h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c | h7439c
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [hlam, p7439_0]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h0, h10, h4, h6948, h7435, h7438, hlam, p7439_2]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h0, h4, h6948, h7435, h7438, hlam, p7439_2]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          rcases p7439_3 (m.d 0 1) (by simp) with h7443 | h7443
          · rcases p7439_3 (m.d 1 2) (by simp) with h7444 | h7444
            · linarith only [h0, h7444, hlam]
            · rcases p7439_3 (m.d 1 3) (by simp) with h7446 | h7446
              · linarith only [h1, h7446, hlam]
              · rcases p7439_3 (m.d 1 4) (by simp) with h7448 | h7448
                · linarith only [h7448, hlam, p7439_0]
                · rcases p7439_3 (m.d 1 5) (by simp) with h7450 | h7450
                  · linarith only [h3, h7450, hlam]
                  · rcases h1emax with h7452 | h7452 | h7452 | h7452 | h7452
                    · linarith only [h0, h10, h4, h6948, h7435, h7438, h7452, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases h2bigk with h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c | h7454c
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [hlam, p7454_0]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [h10, h4, h6948, h7435, h7438, hlam, p7454_2]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [h0, h10, h6948, h7435, h7438, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7454_1]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        rcases p7454_3 (m.d 0 2) (by simp) with h7458 | h7458
                        · rcases p7454_3 (m.d 1 2) (by simp) with h7459 | h7459
                          · linarith only [h0, h7459, hlam]
                          · rcases p7454_3 (m.d 2 3) (by simp) with h7461 | h7461
                            · linarith only [h4, h7461, hlam]
                            · linarith only [h7435, h7461, hlam]
                        · linarith only [h7458, hlam, p7454_0]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        rcases p7454_3 (m.d 0 2) (by simp) with h7465 | h7465
                        · rcases p7454_3 (m.d 1 2) (by simp) with h7466 | h7466
                          · linarith only [h0, h7466, hlam]
                          · rcases p7454_3 (m.d 2 3) (by simp) with h7468 | h7468
                            · linarith only [h4, h7468, hlam]
                            · linarith only [h7436, h7468, hlam]
                        · linarith only [h7465, hlam, p7454_0]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [h0, hlam, p7454_1]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [hlam, p7454_0]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [h10, hlam, p7454_0]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [h3576, hlam, p7454_0]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [h4058, hlam, p7454_0]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [h4, hlam, p7454_0]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        rcases p7454_3 (m.d 0 2) (by simp) with h7478 | h7478
                        · rcases p7454_3 (m.d 1 2) (by simp) with h7479 | h7479
                          · linarith only [h7479, hlam, p7454_0]
                          · rcases p7454_3 (m.d 2 3) (by simp) with h7481 | h7481
                            · rcases p7454_3 (m.d 2 4) (by simp) with h7482 | h7482
                              · linarith only [h7435, h7482, hlam]
                              · linarith only [h3576, h7482, hlam]
                            · linarith only [h7481, hlam, p7454_0]
                        · linarith only [h0, h7478, hlam]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [hlam, p7454_0]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [h10, h6948, h7436, h7437, hc12, hc23, hlam, hphi, p7454_1]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [h0, h10, h4, h6948, h7436, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7454_1]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [h5, hlam, p7454_0]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        rcases p7454_3 (m.d 0 2) (by simp) with h7491 | h7491
                        · rcases p7454_3 (m.d 1 2) (by simp) with h7492 | h7492
                          · linarith only [h7492, hlam, p7454_0]
                          · rcases p7454_3 (m.d 2 3) (by simp) with h7494 | h7494
                            · rcases p7454_3 (m.d 2 4) (by simp) with h7495 | h7495
                              · rcases p7454_3 (m.d 2 5) (by simp) with h7496 | h7496
                                · linarith only [h7437, h7496, hlam]
                                · linarith only [h4058, h7496, hlam]
                              · linarith only [h7495, hlam, p7454_0]
                            · linarith only [h10, h7494, hlam]
                        · linarith only [h0, h7491, hlam]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [h7435, hlam, p7454_0]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [hlam, p7454_0]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [h10, h6948, h7436, hc12, hc24, hlam, hphi, p7454_1]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [h6, hlam, p7454_0]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        rcases p7454_3 (m.d 0 2) (by simp) with h7506 | h7506
                        · rcases p7454_3 (m.d 1 2) (by simp) with h7507 | h7507
                          · linarith only [h7507, hlam, p7454_0]
                          · rcases p7454_3 (m.d 2 3) (by simp) with h7509 | h7509
                            · rcases p7454_3 (m.d 2 4) (by simp) with h7510 | h7510
                              · rcases p7454_3 (m.d 2 5) (by simp) with h7511 | h7511
                                · rcases h4bigk with h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [hlam, p7512_0]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    rcases p7512_3 (m.d 0 4) (by simp) with h7514 | h7514
                                    · rcases p7512_3 (m.d 1 4) (by simp) with h7515 | h7515
                                      · linarith only [h2, h7515, hlam]
                                      · rcases p7512_3 (m.d 2 4) (by simp) with h7517 | h7517
                                        · linarith only [h5, h7517, hlam]
                                        · linarith only [h3576, h7517, hlam]
                                    · linarith only [h2, h7514, hlam]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [h0, h4, h7, h7437, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7454_1, p7512_1]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    rcases p7512_3 (m.d 0 4) (by simp) with h7522 | h7522
                                    · rcases p7512_3 (m.d 1 4) (by simp) with h7523 | h7523
                                      · linarith only [h2, h7523, hlam]
                                      · rcases p7512_3 (m.d 2 4) (by simp) with h7525 | h7525
                                        · linarith only [h5, h7525, hlam]
                                        · linarith only [h7435, h7525, hlam]
                                    · linarith only [h7, h7522, hlam]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    rcases p7512_3 (m.d 0 4) (by simp) with h7529 | h7529
                                    · rcases p7512_3 (m.d 1 4) (by simp) with h7530 | h7530
                                      · linarith only [h2, h7530, hlam]
                                      · linarith only [h7434, h7530, hlam]
                                    · linarith only [h7529, hlam, p7512_0]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [h2, hlam, p7512_0]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [hlam, p7512_0]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [h3576, hlam, p7512_1]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [h4129, hlam, p7512_1]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p7439_1, p7512_1]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [h5, hlam, p7512_0]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [h0, h5, hlam, p7439_2, p7512_1]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [hlam, p7512_0]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [h0, h10, h4, h4129, h7435, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7512_1]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    rcases p7512_3 (m.d 0 4) (by simp) with h7543 | h7543
                                    · rcases p7512_3 (m.d 1 4) (by simp) with h7544 | h7544
                                      · linarith only [h3576, h7544, hlam]
                                      · linarith only [h7434, h7544, hlam]
                                    · linarith only [h7543, h9, hlam]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [h7, hlam, p7512_0]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [h0, h4, h7, h7434, hc01, hc45, hlam, hphi, ht0b, ht5b, p7512_1]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [h7435, hlam, p7512_0]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [hlam, p7512_0]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [h0, h4, h7435, hc01, hc45, hlam, hphi, ht0b, ht5b, p7512_1]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [h9, hlam, p7512_0]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [h7434, hlam, p7512_0]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [h7437, hlam, p7512_0]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [h7438, hlam, p7512_0]
                                  · have p7512_0 := h7512c.1
                                    have p7512_1 := h7512c.2.1
                                    have p7512_2 := h7512c.2.2.1
                                    have p7512_3 := h7512c.2.2.2
                                    linarith only [hlam, p7512_0]
                                · linarith only [h7511, hlam, p7454_0]
                              · linarith only [h3576, h7510, hlam]
                            · linarith only [h10, h7509, hlam]
                        · linarith only [h0, h7506, hlam]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [h7436, hlam, p7454_0]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [h7437, hlam, p7454_1]
                      · have p7454_0 := h7454c.1
                        have p7454_1 := h7454c.2.1
                        have p7454_2 := h7454c.2.2.1
                        have p7454_3 := h7454c.2.2.2
                        linarith only [hlam, p7454_0]
                    · rcases h2bigk with h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c | h7565c
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [hlam, p7565_0]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [h10, h4, h4129, h7435, hlam, p7565_2]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [h0, h10, h4129, h7435, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7565_1]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        rcases p7565_3 (m.d 0 2) (by simp) with h7569 | h7569
                        · rcases p7565_3 (m.d 1 2) (by simp) with h7570 | h7570
                          · linarith only [h0, h7570, hlam]
                          · rcases p7565_3 (m.d 2 3) (by simp) with h7572 | h7572
                            · linarith only [h4, h7572, hlam]
                            · linarith only [h7435, h7572, hlam]
                        · linarith only [h7569, hlam, p7565_0]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        rcases p7565_3 (m.d 0 2) (by simp) with h7576 | h7576
                        · rcases p7565_3 (m.d 1 2) (by simp) with h7577 | h7577
                          · linarith only [h0, h7577, hlam]
                          · rcases p7565_3 (m.d 2 3) (by simp) with h7579 | h7579
                            · linarith only [h4, h7579, hlam]
                            · linarith only [h7436, h7579, hlam]
                        · linarith only [h7576, hlam, p7565_0]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [h0, hlam, p7565_1]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [hlam, p7565_0]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [h10, hlam, p7565_0]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [h3576, hlam, p7565_0]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [h4058, hlam, p7565_0]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [h4, hlam, p7565_0]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        rcases p7565_3 (m.d 0 2) (by simp) with h7589 | h7589
                        · rcases p7565_3 (m.d 1 2) (by simp) with h7590 | h7590
                          · linarith only [h7590, hlam, p7565_0]
                          · rcases p7565_3 (m.d 2 3) (by simp) with h7592 | h7592
                            · rcases p7565_3 (m.d 2 4) (by simp) with h7593 | h7593
                              · linarith only [h7435, h7593, hlam]
                              · linarith only [h3576, h7593, hlam]
                            · linarith only [h7592, hlam, p7565_0]
                        · linarith only [h0, h7589, hlam]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [hlam, p7565_0]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [h0, h3576, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7565_1]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7565_1]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [h5, hlam, p7565_0]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        rcases p7565_3 (m.d 0 2) (by simp) with h7602 | h7602
                        · rcases p7565_3 (m.d 1 2) (by simp) with h7603 | h7603
                          · linarith only [h7603, hlam, p7565_0]
                          · rcases p7565_3 (m.d 2 3) (by simp) with h7605 | h7605
                            · rcases p7565_3 (m.d 2 4) (by simp) with h7606 | h7606
                              · rcases p7565_3 (m.d 2 5) (by simp) with h7607 | h7607
                                · linarith only [h7437, h7607, hlam]
                                · linarith only [h4058, h7607, hlam]
                              · linarith only [h7606, hlam, p7565_0]
                            · linarith only [h10, h7605, hlam]
                        · linarith only [h0, h7602, hlam]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [h7435, hlam, p7565_0]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [hlam, p7565_0]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [h10, h6948, h7436, hc12, hc24, hlam, hphi, p7565_1]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [h6, hlam, p7565_0]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        rcases p7565_3 (m.d 0 2) (by simp) with h7617 | h7617
                        · rcases p7565_3 (m.d 1 2) (by simp) with h7618 | h7618
                          · linarith only [h7618, hlam, p7565_0]
                          · rcases p7565_3 (m.d 2 3) (by simp) with h7620 | h7620
                            · rcases p7565_3 (m.d 2 4) (by simp) with h7621 | h7621
                              · rcases p7565_3 (m.d 2 5) (by simp) with h7622 | h7622
                                · rcases h4bigk with h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c | h7623c
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [hlam, p7623_0]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    rcases p7623_3 (m.d 0 4) (by simp) with h7625 | h7625
                                    · rcases p7623_3 (m.d 1 4) (by simp) with h7626 | h7626
                                      · linarith only [h2, h7626, hlam]
                                      · rcases p7623_3 (m.d 2 4) (by simp) with h7628 | h7628
                                        · linarith only [h5, h7628, hlam]
                                        · linarith only [h3576, h7628, hlam]
                                    · linarith only [h2, h7625, hlam]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [h0, h4, h7, h7437, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7565_1, p7623_1]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    rcases p7623_3 (m.d 0 4) (by simp) with h7633 | h7633
                                    · rcases p7623_3 (m.d 1 4) (by simp) with h7634 | h7634
                                      · linarith only [h2, h7634, hlam]
                                      · rcases p7623_3 (m.d 2 4) (by simp) with h7636 | h7636
                                        · linarith only [h5, h7636, hlam]
                                        · linarith only [h7435, h7636, hlam]
                                    · linarith only [h7, h7633, hlam]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    rcases p7623_3 (m.d 0 4) (by simp) with h7640 | h7640
                                    · rcases p7623_3 (m.d 1 4) (by simp) with h7641 | h7641
                                      · linarith only [h2, h7641, hlam]
                                      · linarith only [h7434, h7641, hlam]
                                    · linarith only [h7640, hlam, p7623_0]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [h2, hlam, p7623_0]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [hlam, p7623_0]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [h3576, hlam, p7623_1]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [h4129, hlam, p7623_1]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p7439_1, p7623_1]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [h5, hlam, p7623_0]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [h0, h5, hlam, p7439_2, p7623_1]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [hlam, p7623_0]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [h0, h10, h4, h6948, h7435, h7438, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7623_1]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    rcases p7623_3 (m.d 0 4) (by simp) with h7654 | h7654
                                    · rcases p7623_3 (m.d 1 4) (by simp) with h7655 | h7655
                                      · linarith only [h3576, h7655, hlam]
                                      · linarith only [h7434, h7655, hlam]
                                    · linarith only [h7654, h9, hlam]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [h7, hlam, p7623_0]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [h0, h4, h7, h7434, hc01, hc45, hlam, hphi, ht0b, ht5b, p7623_1]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [h7435, hlam, p7623_0]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [hlam, p7623_0]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [h0, h4, h7435, hc01, hc45, hlam, hphi, ht0b, ht5b, p7623_1]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [h9, hlam, p7623_0]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [h7434, hlam, p7623_0]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [h7437, hlam, p7623_0]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [h7438, hlam, p7623_0]
                                  · have p7623_0 := h7623c.1
                                    have p7623_1 := h7623c.2.1
                                    have p7623_2 := h7623c.2.2.1
                                    have p7623_3 := h7623c.2.2.2
                                    linarith only [hlam, p7623_0]
                                · linarith only [h7622, hlam, p7565_0]
                              · linarith only [h3576, h7621, hlam]
                            · linarith only [h10, h7620, hlam]
                        · linarith only [h0, h7617, hlam]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [h7436, hlam, p7565_0]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [h7437, hlam, p7565_1]
                      · have p7565_0 := h7565c.1
                        have p7565_1 := h7565c.2.1
                        have p7565_2 := h7565c.2.2.1
                        have p7565_3 := h7565c.2.2.2
                        linarith only [hlam, p7565_0]
                    · rcases h2bigk with h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [hlam, p7676_0]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [h10, h4, h4129, h7435, hlam, p7676_2]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [h10, h4129, h7435, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7676_1]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        rcases p7676_3 (m.d 0 2) (by simp) with h7680 | h7680
                        · rcases p7676_3 (m.d 1 2) (by simp) with h7681 | h7681
                          · linarith only [h0, h7681, hlam]
                          · rcases p7676_3 (m.d 2 3) (by simp) with h7683 | h7683
                            · linarith only [h4, h7683, hlam]
                            · linarith only [h7435, h7683, hlam]
                        · linarith only [h7680, hlam, p7676_0]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        rcases p7676_3 (m.d 0 2) (by simp) with h7687 | h7687
                        · rcases p7676_3 (m.d 1 2) (by simp) with h7688 | h7688
                          · linarith only [h0, h7688, hlam]
                          · rcases p7676_3 (m.d 2 3) (by simp) with h7690 | h7690
                            · linarith only [h4, h7690, hlam]
                            · linarith only [h7436, h7690, hlam]
                        · linarith only [h7687, hlam, p7676_0]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [h0, hlam, p7676_1]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [hlam, p7676_0]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [h10, hlam, p7676_0]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [h3576, hlam, p7676_0]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [h4058, hlam, p7676_0]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [h4, hlam, p7676_0]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        rcases p7676_3 (m.d 0 2) (by simp) with h7700 | h7700
                        · rcases p7676_3 (m.d 1 2) (by simp) with h7701 | h7701
                          · linarith only [h7701, hlam, p7676_0]
                          · rcases p7676_3 (m.d 2 3) (by simp) with h7703 | h7703
                            · rcases p7676_3 (m.d 2 4) (by simp) with h7704 | h7704
                              · linarith only [h7435, h7704, hlam]
                              · linarith only [h3576, h7704, hlam]
                            · linarith only [h7703, hlam, p7676_0]
                        · linarith only [h0, h7700, hlam]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [hlam, p7676_0]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [h0, h10, h4, h6948, h7436, h7437, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7676_1]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [h0, h10, h4, h6948, h7436, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7676_1]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [h5, hlam, p7676_0]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        rcases p7676_3 (m.d 0 2) (by simp) with h7713 | h7713
                        · rcases p7676_3 (m.d 1 2) (by simp) with h7714 | h7714
                          · linarith only [h7714, hlam, p7676_0]
                          · rcases p7676_3 (m.d 2 3) (by simp) with h7716 | h7716
                            · rcases p7676_3 (m.d 2 4) (by simp) with h7717 | h7717
                              · rcases p7676_3 (m.d 2 5) (by simp) with h7718 | h7718
                                · linarith only [h7437, h7718, hlam]
                                · linarith only [h4058, h7718, hlam]
                              · linarith only [h7717, hlam, p7676_0]
                            · linarith only [h10, h7716, hlam]
                        · linarith only [h0, h7713, hlam]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [h7435, hlam, p7676_0]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [hlam, p7676_0]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [h10, h6948, h7436, hc12, hc24, hlam, hphi, p7676_1]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [h6, hlam, p7676_0]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        rcases p7676_3 (m.d 0 2) (by simp) with h7728 | h7728
                        · rcases p7676_3 (m.d 1 2) (by simp) with h7729 | h7729
                          · linarith only [h7729, hlam, p7676_0]
                          · rcases p7676_3 (m.d 2 3) (by simp) with h7731 | h7731
                            · rcases p7676_3 (m.d 2 4) (by simp) with h7732 | h7732
                              · rcases p7676_3 (m.d 2 5) (by simp) with h7733 | h7733
                                · rcases h4bigk with h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c | h7734c
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [hlam, p7734_0]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    rcases p7734_3 (m.d 0 4) (by simp) with h7736 | h7736
                                    · rcases p7734_3 (m.d 1 4) (by simp) with h7737 | h7737
                                      · linarith only [h2, h7737, hlam]
                                      · rcases p7734_3 (m.d 2 4) (by simp) with h7739 | h7739
                                        · linarith only [h5, h7739, hlam]
                                        · linarith only [h3576, h7739, hlam]
                                    · linarith only [h2, h7736, hlam]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [h7437, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7676_1, p7734_1]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    rcases p7734_3 (m.d 0 4) (by simp) with h7744 | h7744
                                    · rcases p7734_3 (m.d 1 4) (by simp) with h7745 | h7745
                                      · linarith only [h2, h7745, hlam]
                                      · rcases p7734_3 (m.d 2 4) (by simp) with h7747 | h7747
                                        · linarith only [h5, h7747, hlam]
                                        · linarith only [h7435, h7747, hlam]
                                    · linarith only [h7, h7744, hlam]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    rcases p7734_3 (m.d 0 4) (by simp) with h7751 | h7751
                                    · rcases p7734_3 (m.d 1 4) (by simp) with h7752 | h7752
                                      · linarith only [h2, h7752, hlam]
                                      · linarith only [h7434, h7752, hlam]
                                    · linarith only [h7751, hlam, p7734_0]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [h2, hlam, p7734_0]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [hlam, p7734_0]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [h3576, hlam, p7734_1]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [h4129, hlam, p7734_1]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p7439_1, p7734_1]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [h5, hlam, p7734_0]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [h0, h5, hlam, p7439_2, p7734_1]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [hlam, p7734_0]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [h0, h10, h4, h6948, h7435, h7438, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7734_1]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    rcases p7734_3 (m.d 0 4) (by simp) with h7765 | h7765
                                    · rcases p7734_3 (m.d 1 4) (by simp) with h7766 | h7766
                                      · linarith only [h3576, h7766, hlam]
                                      · linarith only [h7434, h7766, hlam]
                                    · linarith only [h7765, h9, hlam]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [h7, hlam, p7734_0]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [h0, h4, h7, h7434, hc01, hc45, hlam, hphi, ht0b, ht5b, p7734_1]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [h7435, hlam, p7734_0]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [hlam, p7734_0]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [h0, h4, h7435, hc01, hc45, hlam, hphi, ht0b, ht5b, p7734_1]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [h9, hlam, p7734_0]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [h7434, hlam, p7734_0]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [h7437, hlam, p7734_0]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [h7438, hlam, p7734_0]
                                  · have p7734_0 := h7734c.1
                                    have p7734_1 := h7734c.2.1
                                    have p7734_2 := h7734c.2.2.1
                                    have p7734_3 := h7734c.2.2.2
                                    linarith only [hlam, p7734_0]
                                · linarith only [h7733, hlam, p7676_0]
                              · linarith only [h3576, h7732, hlam]
                            · linarith only [h10, h7731, hlam]
                        · linarith only [h0, h7728, hlam]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [h7436, hlam, p7676_0]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [h7437, hlam, p7676_1]
                      · have p7676_0 := h7676c.1
                        have p7676_1 := h7676c.2.1
                        have p7676_2 := h7676c.2.2.1
                        have p7676_3 := h7676c.2.2.2
                        linarith only [hlam, p7676_0]
                    · rcases h2bigk with h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c | h7787c
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [hlam, p7787_0]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [h10, h4, h4129, h7435, hlam, p7787_2]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [h10, h4129, h7435, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7787_1]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        rcases p7787_3 (m.d 0 2) (by simp) with h7791 | h7791
                        · rcases p7787_3 (m.d 1 2) (by simp) with h7792 | h7792
                          · linarith only [h0, h7792, hlam]
                          · rcases p7787_3 (m.d 2 3) (by simp) with h7794 | h7794
                            · linarith only [h4, h7794, hlam]
                            · linarith only [h7435, h7794, hlam]
                        · linarith only [h7791, hlam, p7787_0]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        rcases p7787_3 (m.d 0 2) (by simp) with h7798 | h7798
                        · rcases p7787_3 (m.d 1 2) (by simp) with h7799 | h7799
                          · linarith only [h0, h7799, hlam]
                          · rcases p7787_3 (m.d 2 3) (by simp) with h7801 | h7801
                            · linarith only [h4, h7801, hlam]
                            · linarith only [h7436, h7801, hlam]
                        · linarith only [h7798, hlam, p7787_0]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [h0, hlam, p7787_1]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [hlam, p7787_0]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [h10, hlam, p7787_0]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [h3576, hlam, p7787_0]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [h4058, hlam, p7787_0]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [h4, hlam, p7787_0]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        rcases p7787_3 (m.d 0 2) (by simp) with h7811 | h7811
                        · rcases p7787_3 (m.d 1 2) (by simp) with h7812 | h7812
                          · linarith only [h7812, hlam, p7787_0]
                          · rcases p7787_3 (m.d 2 3) (by simp) with h7814 | h7814
                            · rcases p7787_3 (m.d 2 4) (by simp) with h7815 | h7815
                              · linarith only [h7435, h7815, hlam]
                              · linarith only [h3576, h7815, hlam]
                            · linarith only [h7814, hlam, p7787_0]
                        · linarith only [h0, h7811, hlam]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [hlam, p7787_0]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [h0, h3576, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7787_1]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7787_1]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [h5, hlam, p7787_0]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        rcases p7787_3 (m.d 0 2) (by simp) with h7824 | h7824
                        · rcases p7787_3 (m.d 1 2) (by simp) with h7825 | h7825
                          · linarith only [h7825, hlam, p7787_0]
                          · rcases p7787_3 (m.d 2 3) (by simp) with h7827 | h7827
                            · rcases p7787_3 (m.d 2 4) (by simp) with h7828 | h7828
                              · rcases p7787_3 (m.d 2 5) (by simp) with h7829 | h7829
                                · linarith only [h7437, h7829, hlam]
                                · linarith only [h4058, h7829, hlam]
                              · linarith only [h7828, hlam, p7787_0]
                            · linarith only [h10, h7827, hlam]
                        · linarith only [h0, h7824, hlam]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [h7435, hlam, p7787_0]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [hlam, p7787_0]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [h10, h6948, h7436, hc12, hc24, hlam, hphi, p7787_1]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [h6, hlam, p7787_0]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        rcases p7787_3 (m.d 0 2) (by simp) with h7839 | h7839
                        · rcases p7787_3 (m.d 1 2) (by simp) with h7840 | h7840
                          · linarith only [h7840, hlam, p7787_0]
                          · rcases p7787_3 (m.d 2 3) (by simp) with h7842 | h7842
                            · rcases p7787_3 (m.d 2 4) (by simp) with h7843 | h7843
                              · rcases p7787_3 (m.d 2 5) (by simp) with h7844 | h7844
                                · rcases h4bigk with h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c | h7845c
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [hlam, p7845_0]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    rcases p7845_3 (m.d 0 4) (by simp) with h7847 | h7847
                                    · rcases p7845_3 (m.d 1 4) (by simp) with h7848 | h7848
                                      · linarith only [h2, h7848, hlam]
                                      · rcases p7845_3 (m.d 2 4) (by simp) with h7850 | h7850
                                        · linarith only [h5, h7850, hlam]
                                        · linarith only [h3576, h7850, hlam]
                                    · linarith only [h2, h7847, hlam]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [h7437, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7787_1, p7845_1]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    rcases p7845_3 (m.d 0 4) (by simp) with h7855 | h7855
                                    · rcases p7845_3 (m.d 1 4) (by simp) with h7856 | h7856
                                      · linarith only [h2, h7856, hlam]
                                      · rcases p7845_3 (m.d 2 4) (by simp) with h7858 | h7858
                                        · linarith only [h5, h7858, hlam]
                                        · linarith only [h7435, h7858, hlam]
                                    · linarith only [h7, h7855, hlam]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    rcases p7845_3 (m.d 0 4) (by simp) with h7862 | h7862
                                    · rcases p7845_3 (m.d 1 4) (by simp) with h7863 | h7863
                                      · linarith only [h2, h7863, hlam]
                                      · linarith only [h7434, h7863, hlam]
                                    · linarith only [h7862, hlam, p7845_0]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [h2, hlam, p7845_0]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [hlam, p7845_0]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [h3576, hlam, p7845_1]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [h4129, hlam, p7845_1]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p7439_1, p7845_1]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [h5, hlam, p7845_0]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [h0, h5, hlam, p7439_2, p7845_1]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [hlam, p7845_0]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [h0, h10, h4, h6948, h7435, h7438, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7845_1]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    rcases p7845_3 (m.d 0 4) (by simp) with h7876 | h7876
                                    · rcases p7845_3 (m.d 1 4) (by simp) with h7877 | h7877
                                      · linarith only [h3576, h7877, hlam]
                                      · linarith only [h7434, h7877, hlam]
                                    · linarith only [h7876, h9, hlam]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [h7, hlam, p7845_0]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [h0, h4, h7, h7434, hc01, hc45, hlam, hphi, ht0b, ht5b, p7845_1]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [h7435, hlam, p7845_0]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [hlam, p7845_0]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [h0, h4, h7435, hc01, hc45, hlam, hphi, ht0b, ht5b, p7845_1]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [h9, hlam, p7845_0]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [h7434, hlam, p7845_0]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [h7437, hlam, p7845_0]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [h7438, hlam, p7845_0]
                                  · have p7845_0 := h7845c.1
                                    have p7845_1 := h7845c.2.1
                                    have p7845_2 := h7845c.2.2.1
                                    have p7845_3 := h7845c.2.2.2
                                    linarith only [hlam, p7845_0]
                                · linarith only [h7844, hlam, p7787_0]
                              · linarith only [h3576, h7843, hlam]
                            · linarith only [h10, h7842, hlam]
                        · linarith only [h0, h7839, hlam]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [h7436, hlam, p7787_0]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [h7437, hlam, p7787_1]
                      · have p7787_0 := h7787c.1
                        have p7787_1 := h7787c.2.1
                        have p7787_2 := h7787c.2.2.1
                        have p7787_3 := h7787c.2.2.2
                        linarith only [hlam, p7787_0]
          · linarith only [h7443, hlam, p7439_0]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          rcases p7439_3 (m.d 0 1) (by simp) with h7899 | h7899
          · rcases p7439_3 (m.d 1 2) (by simp) with h7900 | h7900
            · linarith only [h0, h7900, hlam]
            · rcases p7439_3 (m.d 1 3) (by simp) with h7902 | h7902
              · linarith only [h1, h7902, hlam]
              · rcases p7439_3 (m.d 1 4) (by simp) with h7904 | h7904
                · linarith only [h2, h7904, hlam]
                · linarith only [h7434, h7904, hlam]
          · linarith only [h7899, hlam, p7439_0]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h0, hlam, p7439_0]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [hlam, p7439_0]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h10, hlam, p7439_1]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h3576, hlam, p7439_1]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h4058, hlam, p7439_1]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h1, hlam, p7439_0]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h6948, hc12, hc35, hlam, hphi, ht23, p7439_1]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [hlam, p7439_0]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h4129, hlam, p7439_0]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h6948, hlam, p7439_1]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h2, hlam, p7439_0]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h0, h4, h4129, h7435, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7439_1]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h0, h4, h4129, h7435, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p7439_1]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [hlam, p7439_0]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h0, h4, h4129, h7435, hc01, hc15, hlam, hphi, ht0b, ht5b, p7439_1]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h3, hlam, p7439_0]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h0, h4, h4129, h7434, h7435, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7439_1]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h0, h10, h4, h4129, h7434, h7435, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7439_1]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [h7434, hlam, p7439_0]
        · have p7439_0 := h7439c.1
          have p7439_1 := h7439c.2.1
          have p7439_2 := h7439c.2.2.1
          have p7439_3 := h7439c.2.2.2
          linarith only [hlam, p7439_0]
      · linarith only [h4129, h7434, h7438, hlam]
    · linarith only [h2, h3576, h7434, h7437, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
  · linarith only [h0, h10, h4, h4129, h7435, h7436, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

end R2N4
