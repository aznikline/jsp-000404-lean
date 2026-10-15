import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_45S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h475 | h475
  · rcases m.htr 0 3 5 (by decide) (by decide) with h476 | h476
    · rcases m.htr 1 2 3 (by decide) (by decide) with h477 | h477
      · linarith only [h0, h4, h477, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h479 | h479
        · rcases m.htr 1 2 5 (by decide) (by decide) with h480 | h480
          · linarith only [h0, h480, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h482 | h482
            · rcases m.htr 1 3 5 (by decide) (by decide) with h483 | h483
              · linarith only [h1, h483, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h485 | h485
                · linarith only [h2, h485, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h487 | h487
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h488 | h488
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h489 | h489
                      · linarith only [h476, h477, h479, h483, h485, h489, hc03, hlam, hphi, ht0b, ht5b, u5ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h491 | h491
                        · linarith only [h477, h479, h483, h487, h488, h489, h491, hlam]
                        · rcases h1bigk with h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [hlam, p493_0]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            rcases p493_3 (m.d 0 1) (by simp) with h495 | h495
                            · rcases p493_3 (m.d 1 2) (by simp) with h496 | h496
                              · linarith only [h496, hlam, p493_0]
                              · rcases p493_3 (m.d 1 3) (by simp) with h498 | h498
                                · linarith only [h1, h498, hlam]
                                · linarith only [h477, h498, hlam]
                            · linarith only [h495, hlam, p493_0]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            rcases p493_3 (m.d 0 1) (by simp) with h502 | h502
                            · rcases p493_3 (m.d 1 2) (by simp) with h503 | h503
                              · linarith only [h0, h503, hlam]
                              · rcases p493_3 (m.d 1 3) (by simp) with h505 | h505
                                · linarith only [h505, hlam, p493_0]
                                · rcases p493_3 (m.d 1 4) (by simp) with h507 | h507
                                  · linarith only [h2, h507, hlam]
                                  · rcases p493_3 (m.d 1 5) (by simp) with h509 | h509
                                    · linarith only [h3, h509, hlam]
                                    · linarith only [h483, h509, hlam]
                            · linarith only [h502, hlam, p493_0]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            rcases p493_3 (m.d 0 1) (by simp) with h513 | h513
                            · rcases p493_3 (m.d 1 2) (by simp) with h514 | h514
                              · linarith only [h0, h514, hlam]
                              · linarith only [h479, h514, hlam]
                            · linarith only [h513, hlam, p493_0]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht5b, p493_1, u5ehi1]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [h0, hlam, p493_0]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [hlam, p493_0]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [h477, hlam, p493_0]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [h4, h476, h477, h483, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p493_1]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [h480, hlam, p493_0]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [h1, hlam, p493_0]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [h4, h476, h483, hc12, hc23, hlam, hphi, p493_1]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [hlam, p493_0]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [h4, h476, h479, h483, h487, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p493_1]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [h483, hlam, p493_1]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [h2, hlam, p493_0]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [h479, hlam, p493_1]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [h482, hlam, p493_0]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [hlam, p493_0]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [h485, hlam, p493_1]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [h3, hlam, p493_0]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [h3, h479, h487, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p493_1]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [h4, h476, h477, h479, h483, h487, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p493_1]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            rcases p493_3 (m.d 0 1) (by simp) with h537 | h537
                            · rcases p493_3 (m.d 1 2) (by simp) with h538 | h538
                              · linarith only [h480, h538, hlam]
                              · linarith only [h479, h538, hlam]
                            · linarith only [h2, h537, hlam]
                          · have p493_0 := h493c.1
                            have p493_1 := h493c.2.1
                            have p493_2 := h493c.2.2.1
                            have p493_3 := h493c.2.2.2
                            linarith only [hlam, p493_0]
                    · linarith only [h4, h476, h488, hlam]
                  · linarith only [h4, h476, h483, h487, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
            · linarith only [h477, h479, h482, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h546 | h546
          · linarith only [h479, h546, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h548 | h548
            · rcases m.htr 1 3 5 (by decide) (by decide) with h549 | h549
              · linarith only [h1, h549, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h551 | h551
                · linarith only [h476, h548, h549, h551, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h553 | h553
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h554 | h554
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h555 | h555
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h556 | h556
                        · linarith only [h4, h476, h548, h549, h551, h556, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                        · rcases h1bigk with h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [hlam, p558_0]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            rcases p558_3 (m.d 0 1) (by simp) with h560 | h560
                            · rcases p558_3 (m.d 1 2) (by simp) with h561 | h561
                              · linarith only [h561, hlam, p558_0]
                              · rcases p558_3 (m.d 1 3) (by simp) with h563 | h563
                                · linarith only [h1, h563, hlam]
                                · linarith only [h477, h563, hlam]
                            · linarith only [h560, hlam, p558_0]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            rcases p558_3 (m.d 0 1) (by simp) with h567 | h567
                            · rcases p558_3 (m.d 1 2) (by simp) with h568 | h568
                              · linarith only [h0, h568, hlam]
                              · rcases p558_3 (m.d 1 3) (by simp) with h570 | h570
                                · linarith only [h570, hlam, p558_0]
                                · rcases p558_3 (m.d 1 4) (by simp) with h572 | h572
                                  · linarith only [h2, h572, hlam]
                                  · rcases p558_3 (m.d 1 5) (by simp) with h574 | h574
                                    · linarith only [h3, h574, hlam]
                                    · linarith only [h549, h574, hlam]
                            · linarith only [h567, hlam, p558_0]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            rcases p558_3 (m.d 0 1) (by simp) with h578 | h578
                            · rcases p558_3 (m.d 1 2) (by simp) with h579 | h579
                              · linarith only [h0, h579, hlam]
                              · rcases p558_3 (m.d 1 3) (by simp) with h581 | h581
                                · linarith only [h1, h581, hlam]
                                · linarith only [h548, h581, hlam]
                            · linarith only [h578, hlam, p558_0]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht5b, p558_1, u5ehi1]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [h0, hlam, p558_0]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [hlam, p558_0]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [h477, hlam, p558_0]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [h479, hlam, p558_0]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [h546, hlam, p558_0]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [h1, hlam, p558_0]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [h549, h553, h555, h556, hc12, hc23, hlam, hphi, p558_1]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [hlam, p558_0]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [h549, h553, h555, h556, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p558_1]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [h549, hlam, p558_1]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [h2, hlam, p558_0]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [h548, h549, h553, h555, h556, hc12, hc23, hlam, hphi, p558_1]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [h548, hlam, p558_0]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [hlam, p558_0]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [h551, hlam, p558_1]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [h3, hlam, p558_0]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [h549, h553, h555, h556, hc12, hc23, hlam, hphi, p558_1]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [h548, h549, h553, h555, h556, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p558_1]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [h479, h549, h553, h555, h556, hc12, hc23, hlam, hphi, p558_1]
                          · have p558_0 := h558c.1
                            have p558_1 := h558c.2.1
                            have p558_2 := h558c.2.2.1
                            have p558_3 := h558c.2.2.2
                            linarith only [hlam, p558_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h606 | h606
                        · linarith only [h548, h606, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · rcases h1bigk with h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [hlam, p608_0]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            rcases p608_3 (m.d 0 1) (by simp) with h610 | h610
                            · rcases p608_3 (m.d 1 2) (by simp) with h611 | h611
                              · linarith only [h611, hlam, p608_0]
                              · rcases p608_3 (m.d 1 3) (by simp) with h613 | h613
                                · linarith only [h1, h613, hlam]
                                · linarith only [h477, h613, hlam]
                            · linarith only [h610, hlam, p608_0]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            rcases p608_3 (m.d 0 1) (by simp) with h617 | h617
                            · rcases p608_3 (m.d 1 2) (by simp) with h618 | h618
                              · linarith only [h0, h618, hlam]
                              · rcases p608_3 (m.d 1 3) (by simp) with h620 | h620
                                · linarith only [h620, hlam, p608_0]
                                · rcases p608_3 (m.d 1 4) (by simp) with h622 | h622
                                  · linarith only [h2, h622, hlam]
                                  · rcases p608_3 (m.d 1 5) (by simp) with h624 | h624
                                    · linarith only [h3, h624, hlam]
                                    · linarith only [h549, h624, hlam]
                            · linarith only [h617, hlam, p608_0]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            rcases p608_3 (m.d 0 1) (by simp) with h628 | h628
                            · rcases p608_3 (m.d 1 2) (by simp) with h629 | h629
                              · linarith only [h0, h629, hlam]
                              · rcases p608_3 (m.d 1 3) (by simp) with h631 | h631
                                · linarith only [h1, h631, hlam]
                                · linarith only [h548, h631, hlam]
                            · linarith only [h628, hlam, p608_0]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht5b, p608_1, u5ehi1]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [h0, hlam, p608_0]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [hlam, p608_0]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [h477, hlam, p608_0]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [h479, hlam, p608_0]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [h546, hlam, p608_0]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [h1, hlam, p608_0]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [h549, h554, hc12, hc25, hlam, hphi, p608_1]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [hlam, p608_0]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [h4, h476, h479, h549, hc12, hc23, hlam, hphi, p608_1]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [h549, hlam, p608_1]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [h2, hlam, p608_0]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [h479, h555, hc12, hc45, hlam, hphi, ht23, ht34, p608_1]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [h548, hlam, p608_0]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [hlam, p608_0]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [h551, hlam, p608_1]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [h3, hlam, p608_0]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [h4, h476, h549, hc12, hc23, hlam, hphi, p608_1]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [h4, h476, h548, h549, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p608_1]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [h4, h476, h479, h549, hc12, hc23, hlam, hphi, p608_1]
                          · have p608_0 := h608c.1
                            have p608_1 := h608c.2.1
                            have p608_2 := h608c.2.2.1
                            have p608_3 := h608c.2.2.2
                            linarith only [hlam, p608_0]
                    · linarith only [h4, h476, h554, hlam]
                  · linarith only [h4, h476, h548, h553, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h658 | h658
              · linarith only [h1, h658, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h660 | h660
                · linarith only [h475, h548, h660, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h662 | h662
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h663 | h663
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h664 | h664
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h665 | h665
                        · linarith only [h4, h475, h665, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · linarith only [h477, h548, h662, h664, h665, hc12, hc23, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h668 | h668
                        · linarith only [h4, h475, h664, h668, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · rcases h1bigk with h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [hlam, p670_0]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            rcases p670_3 (m.d 0 1) (by simp) with h672 | h672
                            · rcases p670_3 (m.d 1 2) (by simp) with h673 | h673
                              · linarith only [h673, hlam, p670_0]
                              · rcases p670_3 (m.d 1 3) (by simp) with h675 | h675
                                · linarith only [h1, h675, hlam]
                                · linarith only [h477, h675, hlam]
                            · linarith only [h672, hlam, p670_0]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            rcases p670_3 (m.d 0 1) (by simp) with h679 | h679
                            · rcases p670_3 (m.d 1 2) (by simp) with h680 | h680
                              · linarith only [h0, h680, hlam]
                              · rcases p670_3 (m.d 1 3) (by simp) with h682 | h682
                                · linarith only [h682, hlam, p670_0]
                                · rcases p670_3 (m.d 1 4) (by simp) with h684 | h684
                                  · linarith only [h2, h684, hlam]
                                  · linarith only [h548, h684, hlam]
                            · linarith only [h679, hlam, p670_0]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            rcases p670_3 (m.d 0 1) (by simp) with h688 | h688
                            · rcases p670_3 (m.d 1 2) (by simp) with h689 | h689
                              · linarith only [h0, h689, hlam]
                              · rcases p670_3 (m.d 1 3) (by simp) with h691 | h691
                                · linarith only [h1, h691, hlam]
                                · rcases p670_3 (m.d 1 4) (by simp) with h693 | h693
                                  · linarith only [h693, hlam, p670_0]
                                  · rcases p670_3 (m.d 1 5) (by simp) with h695 | h695
                                    · linarith only [h3, h695, hlam]
                                    · linarith only [h660, h695, hlam]
                            · linarith only [h688, hlam, p670_0]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht5b, p670_1, u5ehi1]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [h0, hlam, p670_0]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [hlam, p670_0]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [h477, hlam, p670_0]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [h479, hlam, p670_0]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [h546, hlam, p670_0]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [h1, hlam, p670_0]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [h548, hc12, hc34, hlam, hphi, ht23, p670_1]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [hlam, p670_0]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [h548, hlam, p670_1]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [h658, hlam, p670_1]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [h2, hlam, p670_0]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [h479, h664, hc12, hc45, hlam, hphi, ht23, ht34, p670_1]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [h479, h664, hc13, hc45, hlam, hphi, ht34, p670_1]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [hlam, p670_0]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [h660, hlam, p670_1]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [h3, hlam, p670_0]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [h4, h476, h658, hc12, hc23, hlam, hphi, p670_1]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [h4, h476, h477, h658, hc12, hc23, hlam, hphi, p670_1]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [h4, h476, h479, h658, hc12, hc23, hlam, hphi, p670_1]
                          · have p670_0 := h670c.1
                            have p670_1 := h670c.2.1
                            have p670_2 := h670c.2.2.1
                            have p670_3 := h670c.2.2.2
                            linarith only [hlam, p670_0]
                    · linarith only [h4, h476, h663, hlam]
                  · linarith only [h4, h475, h662, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h722 | h722
      · linarith only [h0, h4, h722, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h724 | h724
        · rcases m.htr 1 2 5 (by decide) (by decide) with h725 | h725
          · linarith only [h0, h4, h725, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h727 | h727
            · rcases m.htr 1 3 5 (by decide) (by decide) with h728 | h728
              · linarith only [h1, h476, h728, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h730 | h730
                · linarith only [h2, h730, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h732 | h732
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h733 | h733
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h734 | h734
                      · linarith only [h1, h476, h722, h724, h730, h733, h734, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h736 | h736
                        · linarith only [h1, h476, h722, h724, h732, h733, h734, h736, hlam]
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
                                · linarith only [h722, h743, hlam]
                            · linarith only [h740, hlam, p738_0]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            rcases p738_3 (m.d 0 1) (by simp) with h747 | h747
                            · rcases p738_3 (m.d 1 2) (by simp) with h748 | h748
                              · linarith only [h0, h748, hlam]
                              · rcases p738_3 (m.d 1 3) (by simp) with h750 | h750
                                · linarith only [h750, hlam, p738_0]
                                · rcases p738_3 (m.d 1 4) (by simp) with h752 | h752
                                  · linarith only [h2, h752, hlam]
                                  · rcases p738_3 (m.d 1 5) (by simp) with h754 | h754
                                    · linarith only [h3, h754, hlam]
                                    · linarith only [h728, h754, hlam]
                            · linarith only [h747, hlam, p738_0]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            rcases p738_3 (m.d 0 1) (by simp) with h758 | h758
                            · rcases p738_3 (m.d 1 2) (by simp) with h759 | h759
                              · linarith only [h0, h759, hlam]
                              · linarith only [h724, h759, hlam]
                            · linarith only [h758, hlam, p738_0]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht5b, p738_1, u5ehi1]
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
                            linarith only [h722, hlam, p738_0]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            linarith only [h1, h476, h722, h733, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p738_1]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            linarith only [h725, hlam, p738_0]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            linarith only [h1, hlam, p738_0]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            linarith only [h1, h476, h733, hc12, hc23, hlam, hphi, p738_1]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            linarith only [hlam, p738_0]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            linarith only [h1, h476, h724, h732, h733, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p738_1]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            linarith only [h728, hlam, p738_1]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            linarith only [h2, hlam, p738_0]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            linarith only [h724, hlam, p738_1]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            linarith only [h727, hlam, p738_0]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            linarith only [hlam, p738_0]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            linarith only [h730, hlam, p738_1]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            linarith only [h3, hlam, p738_0]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            linarith only [h3, h724, h732, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p738_1]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            linarith only [h3, h476, h722, h724, h732, h733, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p738_1]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            rcases p738_3 (m.d 0 1) (by simp) with h782 | h782
                            · rcases p738_3 (m.d 1 2) (by simp) with h783 | h783
                              · linarith only [h725, h783, hlam]
                              · linarith only [h724, h783, hlam]
                            · linarith only [h2, h782, hlam]
                          · have p738_0 := h738c.1
                            have p738_1 := h738c.2.1
                            have p738_2 := h738c.2.2.1
                            have p738_3 := h738c.2.2.2
                            linarith only [hlam, p738_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h788 | h788
                      · linarith only [h0, h4, h724, h733, h788, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h790 | h790
                        · linarith only [h0, h4, h724, h725, h732, h733, h788, h790, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h0, h4, h724, h732, h733, h790, hc34, hc45, hlam, hphi]
                  · linarith only [h0, h4, h475, h724, h732, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h475, h476, h722, h724, h727, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h795 | h795
          · linarith only [h724, h795, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h797 | h797
            · rcases m.htr 1 3 5 (by decide) (by decide) with h798 | h798
              · linarith only [h1, h476, h798, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h800 | h800
                · linarith only [h2, h475, h476, h800, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h802 | h802
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h803 | h803
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h804 | h804
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h805 | h805
                        · linarith only [h475, h476, h724, h800, h803, h805, hc12, hc23, hlam, hphi]
                        · rcases h1bigk with h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [hlam, p807_0]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            rcases p807_3 (m.d 0 1) (by simp) with h809 | h809
                            · rcases p807_3 (m.d 1 2) (by simp) with h810 | h810
                              · linarith only [h810, hlam, p807_0]
                              · rcases p807_3 (m.d 1 3) (by simp) with h812 | h812
                                · linarith only [h1, h812, hlam]
                                · linarith only [h722, h812, hlam]
                            · linarith only [h809, hlam, p807_0]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            rcases p807_3 (m.d 0 1) (by simp) with h816 | h816
                            · rcases p807_3 (m.d 1 2) (by simp) with h817 | h817
                              · linarith only [h0, h817, hlam]
                              · rcases p807_3 (m.d 1 3) (by simp) with h819 | h819
                                · linarith only [h819, hlam, p807_0]
                                · rcases p807_3 (m.d 1 4) (by simp) with h821 | h821
                                  · linarith only [h2, h821, hlam]
                                  · rcases p807_3 (m.d 1 5) (by simp) with h823 | h823
                                    · linarith only [h3, h823, hlam]
                                    · linarith only [h798, h823, hlam]
                            · linarith only [h816, hlam, p807_0]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            rcases p807_3 (m.d 0 1) (by simp) with h827 | h827
                            · rcases p807_3 (m.d 1 2) (by simp) with h828 | h828
                              · linarith only [h0, h828, hlam]
                              · rcases p807_3 (m.d 1 3) (by simp) with h830 | h830
                                · linarith only [h1, h830, hlam]
                                · linarith only [h797, h830, hlam]
                            · linarith only [h827, hlam, p807_0]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht5b, p807_1, u5ehi1]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [h0, hlam, p807_0]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [hlam, p807_0]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [h722, hlam, p807_0]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [h724, hlam, p807_0]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [h795, hlam, p807_0]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [h1, hlam, p807_0]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [h1, h476, h802, h804, h805, hc12, hc23, hlam, hphi, p807_1]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [hlam, p807_0]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [h1, h476, h724, h802, h804, h805, hc12, hc23, hlam, hphi, p807_1]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [h798, hlam, p807_1]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [h2, hlam, p807_0]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [h2, h475, h476, h802, h804, h805, hc12, hc23, hlam, hphi, p807_1]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [h797, hlam, p807_0]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [hlam, p807_0]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [h800, hlam, p807_1]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [h3, hlam, p807_0]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [h3, h476, h802, h804, h805, hc12, hc23, hlam, hphi, p807_1]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [h3, h476, h797, h802, h804, h805, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p807_1]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [h3, h476, h724, h802, h804, h805, hc12, hc23, hlam, hphi, p807_1]
                          · have p807_0 := h807c.1
                            have p807_1 := h807c.2.1
                            have p807_2 := h807c.2.2.1
                            have p807_3 := h807c.2.2.2
                            linarith only [hlam, p807_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h855 | h855
                        · linarith only [h724, h797, h804, h855, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h1bigk with h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            rcases p857_3 (m.d 0 1) (by simp) with h859 | h859
                            · rcases p857_3 (m.d 1 2) (by simp) with h860 | h860
                              · linarith only [h860, hlam, p857_0]
                              · rcases p857_3 (m.d 1 3) (by simp) with h862 | h862
                                · linarith only [h1, h862, hlam]
                                · linarith only [h722, h862, hlam]
                            · linarith only [h859, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            rcases p857_3 (m.d 0 1) (by simp) with h866 | h866
                            · rcases p857_3 (m.d 1 2) (by simp) with h867 | h867
                              · linarith only [h0, h867, hlam]
                              · rcases p857_3 (m.d 1 3) (by simp) with h869 | h869
                                · linarith only [h869, hlam, p857_0]
                                · rcases p857_3 (m.d 1 4) (by simp) with h871 | h871
                                  · linarith only [h2, h871, hlam]
                                  · rcases p857_3 (m.d 1 5) (by simp) with h873 | h873
                                    · linarith only [h3, h873, hlam]
                                    · linarith only [h798, h873, hlam]
                            · linarith only [h866, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            rcases p857_3 (m.d 0 1) (by simp) with h877 | h877
                            · rcases p857_3 (m.d 1 2) (by simp) with h878 | h878
                              · linarith only [h0, h878, hlam]
                              · rcases p857_3 (m.d 1 3) (by simp) with h880 | h880
                                · linarith only [h1, h880, hlam]
                                · linarith only [h797, h880, hlam]
                            · linarith only [h877, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht5b, p857_1, u5ehi1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h0, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h722, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h724, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h795, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h1, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h1, h476, h803, hc12, hc25, hlam, hphi, p857_1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h1, h476, h724, h803, h804, hc12, hc45, hlam, hphi, ht23, ht34, p857_1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h798, hlam, p857_1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h2, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h2, h475, h476, h803, h804, hc12, hc45, hlam, hphi, ht23, ht34, p857_1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h797, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h800, hlam, p857_1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h3, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h3, h476, h803, hc12, hc23, hlam, hphi, p857_1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h3, h476, h722, h803, hc12, hc23, hlam, hphi, p857_1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h3, h476, h724, h803, hc12, hc23, hlam, hphi, p857_1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [hlam, p857_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h905 | h905
                      · linarith only [h800, h802, h803, h905, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h907 | h907
                        · linarith only [h724, h905, h907, hc12, hc34, hlam, hphi, ht23]
                        · rcases h1bigk with h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [hlam, p909_0]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            rcases p909_3 (m.d 0 1) (by simp) with h911 | h911
                            · rcases p909_3 (m.d 1 2) (by simp) with h912 | h912
                              · linarith only [h912, hlam, p909_0]
                              · rcases p909_3 (m.d 1 3) (by simp) with h914 | h914
                                · linarith only [h1, h914, hlam]
                                · linarith only [h722, h914, hlam]
                            · linarith only [h911, hlam, p909_0]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            rcases p909_3 (m.d 0 1) (by simp) with h918 | h918
                            · rcases p909_3 (m.d 1 2) (by simp) with h919 | h919
                              · linarith only [h0, h919, hlam]
                              · rcases p909_3 (m.d 1 3) (by simp) with h921 | h921
                                · linarith only [h921, hlam, p909_0]
                                · rcases p909_3 (m.d 1 4) (by simp) with h923 | h923
                                  · linarith only [h2, h923, hlam]
                                  · rcases p909_3 (m.d 1 5) (by simp) with h925 | h925
                                    · linarith only [h3, h925, hlam]
                                    · linarith only [h798, h925, hlam]
                            · linarith only [h918, hlam, p909_0]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            rcases p909_3 (m.d 0 1) (by simp) with h929 | h929
                            · rcases p909_3 (m.d 1 2) (by simp) with h930 | h930
                              · linarith only [h0, h930, hlam]
                              · rcases p909_3 (m.d 1 3) (by simp) with h932 | h932
                                · linarith only [h1, h932, hlam]
                                · linarith only [h797, h932, hlam]
                            · linarith only [h929, hlam, p909_0]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht5b, p909_1, u5ehi1]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [h0, hlam, p909_0]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [hlam, p909_0]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [h722, hlam, p909_0]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [h724, hlam, p909_0]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [h795, hlam, p909_0]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [h1, hlam, p909_0]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [h1, h4, h803, h907, hc12, hc45, hlam, hphi, ht23, ht34, p909_1]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [hlam, p909_0]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [h1, h4, h803, h907, hc14, hc45, hlam, hphi, p909_1]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [h798, hlam, p909_1]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [h2, hlam, p909_0]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [h2, h4, h475, h803, h907, hc12, hc45, hlam, hphi, ht23, ht34, p909_1]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [h797, hlam, p909_0]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [hlam, p909_0]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [h800, hlam, p909_1]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [h3, hlam, p909_0]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            rcases p909_3 (m.d 0 1) (by simp) with h953 | h953
                            · rcases p909_3 (m.d 1 2) (by simp) with h954 | h954
                              · linarith only [h795, h954, hlam]
                              · rcases p909_3 (m.d 1 3) (by simp) with h956 | h956
                                · linarith only [h798, h956, hlam]
                                · linarith only [h722, h956, hlam]
                            · linarith only [h0, h953, hlam]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [h3, h797, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p909_1]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            rcases p909_3 (m.d 0 1) (by simp) with h961 | h961
                            · rcases p909_3 (m.d 1 2) (by simp) with h962 | h962
                              · linarith only [h795, h962, hlam]
                              · rcases p909_3 (m.d 1 3) (by simp) with h964 | h964
                                · linarith only [h798, h964, hlam]
                                · linarith only [h797, h964, hlam]
                            · linarith only [h2, h961, hlam]
                          · have p909_0 := h909c.1
                            have p909_1 := h909c.2.1
                            have p909_2 := h909c.2.2.1
                            have p909_3 := h909c.2.2.2
                            linarith only [hlam, p909_0]
                  · linarith only [h0, h1, h4, h797, h802, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h475, h476, h797, hc13, hc35, hlam, hphi]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h971 | h971
    · linarith only [h475, h971, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h973 | h973
      · linarith only [h0, h4, h973, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h975 | h975
        · rcases m.htr 1 2 5 (by decide) (by decide) with h976 | h976
          · linarith only [h0, h4, h976, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h978 | h978
            · linarith only [h1, h475, h978, hlam]
            · linarith only [h973, h975, h978, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h981 | h981
          · linarith only [h1, h475, h973, h981, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h983 | h983
            · linarith only [h1, h475, h983, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h985 | h985
              · linarith only [h1, h971, h985, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h987 | h987
                · linarith only [h2, h987, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h989 | h989
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h990 | h990
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h991 | h991
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h992 | h992
                        · linarith only [h973, h983, h987, h989, h992, hc12, hc23, hlam, hphi]
                        · linarith only [h4, h475, h989, h991, h992, hc02, hc23, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h995 | h995
                        · linarith only [h975, h991, h995, hc12, hc34, hlam, hphi, ht23]
                        · rcases h1bigk with h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [hlam, p997_0]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            rcases p997_3 (m.d 0 1) (by simp) with h999 | h999
                            · rcases p997_3 (m.d 1 2) (by simp) with h1000 | h1000
                              · linarith only [h1000, hlam, p997_0]
                              · rcases p997_3 (m.d 1 3) (by simp) with h1002 | h1002
                                · linarith only [h1, h1002, hlam]
                                · linarith only [h1002, h973, hlam]
                            · linarith only [h999, hlam, p997_0]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            rcases p997_3 (m.d 0 1) (by simp) with h1006 | h1006
                            · rcases p997_3 (m.d 1 2) (by simp) with h1007 | h1007
                              · linarith only [h0, h1007, hlam]
                              · rcases p997_3 (m.d 1 3) (by simp) with h1009 | h1009
                                · linarith only [h1009, hlam, p997_0]
                                · rcases p997_3 (m.d 1 4) (by simp) with h1011 | h1011
                                  · linarith only [h1011, h2, hlam]
                                  · linarith only [h1011, h983, hlam]
                            · linarith only [h1006, hlam, p997_0]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            rcases p997_3 (m.d 0 1) (by simp) with h1015 | h1015
                            · rcases p997_3 (m.d 1 2) (by simp) with h1016 | h1016
                              · linarith only [h0, h1016, hlam]
                              · rcases p997_3 (m.d 1 3) (by simp) with h1018 | h1018
                                · linarith only [h1, h1018, hlam]
                                · rcases p997_3 (m.d 1 4) (by simp) with h1020 | h1020
                                  · linarith only [h1020, hlam, p997_0]
                                  · rcases p997_3 (m.d 1 5) (by simp) with h1022 | h1022
                                    · linarith only [h1022, h3, hlam]
                                    · linarith only [h1022, h987, hlam]
                            · linarith only [h1015, hlam, p997_0]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht5b, p997_1, u5ehi1]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [h0, hlam, p997_0]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [hlam, p997_0]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [h973, hlam, p997_0]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [h975, hlam, p997_0]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [h981, hlam, p997_0]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [h1, hlam, p997_0]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [h1, h475, h989, hc12, hc24, hlam, hphi, p997_1]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [hlam, p997_0]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [h983, hlam, p997_1]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [h985, hlam, p997_1]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [h2, hlam, p997_0]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [h2, h475, h989, h991, hc12, hc45, hlam, hphi, ht23, ht34, p997_1]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [h2, h475, h989, h991, hc13, hc45, hlam, hphi, ht34, p997_1]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [hlam, p997_0]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [h987, hlam, p997_1]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [h3, hlam, p997_0]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [h3, h971, h990, hc12, hc23, hlam, hphi, p997_1]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [h3, h971, h973, h990, hc12, hc23, hlam, hphi, p997_1]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [h3, h971, h975, h990, hc12, hc23, hlam, hphi, p997_1]
                          · have p997_0 := h997c.1
                            have p997_1 := h997c.2.1
                            have p997_2 := h997c.2.2.1
                            have p997_3 := h997c.2.2.2
                            linarith only [hlam, p997_0]
                    · linarith only [h1, h475, h973, h989, h990, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1048 | h1048
                    · linarith only [h1048, h989, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1050 | h1050
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1051 | h1051
                        · rcases h1bigk with h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            rcases p1052_3 (m.d 0 1) (by simp) with h1054 | h1054
                            · rcases p1052_3 (m.d 1 2) (by simp) with h1055 | h1055
                              · linarith only [h1055, hlam, p1052_0]
                              · rcases p1052_3 (m.d 1 3) (by simp) with h1057 | h1057
                                · linarith only [h1, h1057, hlam]
                                · linarith only [h1057, h973, hlam]
                            · linarith only [h1054, hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            rcases p1052_3 (m.d 0 1) (by simp) with h1061 | h1061
                            · rcases p1052_3 (m.d 1 2) (by simp) with h1062 | h1062
                              · linarith only [h0, h1062, hlam]
                              · rcases p1052_3 (m.d 1 3) (by simp) with h1064 | h1064
                                · linarith only [h1064, hlam, p1052_0]
                                · rcases p1052_3 (m.d 1 4) (by simp) with h1066 | h1066
                                  · linarith only [h1066, h2, hlam]
                                  · linarith only [h1066, h983, hlam]
                            · linarith only [h1061, hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            rcases p1052_3 (m.d 0 1) (by simp) with h1070 | h1070
                            · rcases p1052_3 (m.d 1 2) (by simp) with h1071 | h1071
                              · linarith only [h0, h1071, hlam]
                              · rcases p1052_3 (m.d 1 3) (by simp) with h1073 | h1073
                                · linarith only [h1, h1073, hlam]
                                · rcases p1052_3 (m.d 1 4) (by simp) with h1075 | h1075
                                  · linarith only [h1075, hlam, p1052_0]
                                  · rcases p1052_3 (m.d 1 5) (by simp) with h1077 | h1077
                                    · linarith only [h1077, h3, hlam]
                                    · linarith only [h1077, h987, hlam]
                            · linarith only [h1070, hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht5b, p1052_1, u5ehi1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h0, hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h973, hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h975, hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h981, hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h1, hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h1050, h983, h987, h989, hc12, hc34, hlam, hphi, ht23, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h983, hlam, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h985, hlam, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h2, hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h1050, h987, h989, hc12, hc34, hlam, hphi, ht23, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h1050, h987, h989, hc13, hc34, hlam, hphi, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h987, hlam, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h3, hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h1050, h987, h989, hc12, hc34, hlam, hphi, ht23, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h1050, h973, h987, h989, hc12, hc34, hlam, hphi, ht23, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h1050, h975, h987, h989, hc12, hc34, hlam, hphi, ht23, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [hlam, p1052_0]
                        · linarith only [h1050, h1051, h989, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1103 | h1103
                        · linarith only [h0, h1050, h1103, h4, h989, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1103, h4, h989, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_13_25_L_I_L_I_H_R_x0_x0_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_11_13_25_L_I_L_I_H_R_x0_x0_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1106 | h1106
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1107 | h1107
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1108 | h1108
      · linarith only [h1, h1108, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1110 | h1110
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1111 | h1111
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1112 | h1112
            · linarith only [h0, h1112, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1114 | h1114
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1115 | h1115
                · linarith only [h1, h1108, h1112, h1115, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                · linarith only [h0, h1110, h1115, h3, hc23, hc35, hlam, hphi]
              · linarith only [h1107, h1108, h1114, hc13, hc35, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1119 | h1119
            · linarith only [h1111, h1119, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1121 | h1121
              · linarith only [h1110, h1111, h1121, hlam]
              · linarith only [h1107, h1108, h1121, hc13, hc35, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1124 | h1124
          · linarith only [h0, h1106, h1110, h1124, h3, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1126 | h1126
            · linarith only [h0, h1106, h1110, h1126, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · linarith only [h0, h1106, h1110, h1126, h3, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1129 | h1129
      · linarith only [h1107, h1129, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1131 | h1131
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1132 | h1132
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1133 | h1133
            · linarith only [h0, h1133, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1135 | h1135
              · linarith only [h1, h1107, h1133, h1135, h3, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1137 | h1137
                · linarith only [h1, h1107, h1129, h1137, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                · linarith only [h0, h1131, h1137, h3, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1140 | h1140
            · linarith only [h1132, h1140, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1142 | h1142
              · linarith only [h1, h1107, h1142, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1144 | h1144
                · linarith only [h1, h1107, h1129, h1144, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                · linarith only [h1131, h1132, h1144, h2, h3, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1147 | h1147
          · linarith only [h0, h1106, h1131, h1147, h3, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1149 | h1149
            · linarith only [h0, h1106, h1131, h1149, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · linarith only [h0, h1106, h1131, h1149, h3, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1152 | h1152
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1153 | h1153
      · linarith only [h1, h1153, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1155 | h1155
        · linarith only [h0, h1106, h1155, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1157 | h1157
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1158 | h1158
            · linarith only [h0, h1158, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1160 | h1160
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1161 | h1161
                · linarith only [h1, h1153, h1158, h1161, h3, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1163 | h1163
                  · linarith only [h1, h1155, h1157, h1161, h1163, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · linarith only [h1, h1160, h1163, h3, hc34, hc45, hlam, hphi]
              · linarith only [h1, h1152, h1155, h1157, h1160, h3, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1167 | h1167
            · linarith only [h1157, h1167, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1169 | h1169
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1170 | h1170
                · linarith only [h1, h1167, h1170, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1172 | h1172
                  · linarith only [h1, h1169, h1170, h1172, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · linarith only [h1, h1169, h1172, h3, hc34, hc45, hlam, hphi]
              · linarith only [h1152, h1153, h1169, hc13, hc35, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1176 | h1176
      · linarith only [h1, h1176, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1178 | h1178
        · linarith only [h0, h1106, h1178, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1180 | h1180
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1181 | h1181
            · linarith only [h1, h1178, h1181, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1183 | h1183
              · linarith only [h1, h1106, h1152, h1181, h1183, h3, hc02, hc25, hlam, hphi]
              · linarith only [h1178, h1180, h1183, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1186 | h1186
            · linarith only [h1180, h1186, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1188 | h1188
              · linarith only [h1, h1152, h1188, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1190 | h1190
                · linarith only [h1, h1176, h1190, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1192 | h1192
                  · linarith only [h1192, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1194 | h1194
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1195 | h1195
                      · linarith only [h1178, h1188, h1190, h1195, h2, h3, hc12, hc23, hlam, hphi]
                      · linarith only [h1106, h1152, h1194, h1195, hc02, hc35, hlam, hphi, ht23]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1198 | h1198
                      · linarith only [h1194, h1198, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1200 | h1200
                        · linarith only [h1178, h1188, h1192, h1200, h2, h3, hc12, hc24, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1202 | h1202
                          · linarith only [h0, h1106, h1194, h1200, h1202, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h1106, h1194, h1202, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_13_25_L_I_L_I_H_R_x0_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_11_13_25_L_I_L_I_H_R_x0_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2 h3

set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1205 | h1205
  · linarith only [h1205, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1207 | h1207
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1208 | h1208
      · linarith only [h1, h1208, h2, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1210 | h1210
        · linarith only [h0, h1207, h1210, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1212 | h1212
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1213 | h1213
            · linarith only [h0, h1213, h2, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1215 | h1215
              · linarith only [h0, h1213, h1215, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1217 | h1217
                · linarith only [h1, h1208, h1213, h1217, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h0, h1212, h1217, h2, hc23, hc34, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1220 | h1220
            · linarith only [h0, h1207, h1212, h1220, h2, hc14, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h0, h1207, h1212, h1220, h2, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1223 | h1223
      · linarith only [h1, h1223, h2, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1225 | h1225
        · linarith only [h1223, h1225, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1227 | h1227
          · linarith only [h0, h1207, h1227, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1229 | h1229
            · linarith only [h0, h1229, h2, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1231 | h1231
              · linarith only [h1, h1227, h1231, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1233 | h1233
                · linarith only [h1, h1223, h1233, h2, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1235 | h1235
                  · linarith only [h1, h1225, h1233, h1235, h2, hc03, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1237 | h1237
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1238 | h1238
                      · linarith only [h1233, h1237, h1238, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1240 | h1240
                        · linarith only [h1205, h1235, h1238, h1240, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1242 | h1242
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1243 | h1243
                            · rcases h1bigk with h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [hlam, p1244_0]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [h1205, h1231, hc12, hc25, hlam, hphi, p1244_1]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [h1205, h1227, h1231, hc12, hc25, hlam, hphi, p1244_1]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [h2, hlam, p1244_0]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [h1205, hlam, p1244_0]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [h0, hlam, p1244_0]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [hlam, p1244_0]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [h1227, hlam, p1244_0]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [h1229, hlam, p1244_0]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [h1231, hlam, p1244_0]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [h1, hlam, p1244_0]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [h1, h1205, h1231, hc12, hc25, hlam, hphi, p1244_1]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [hlam, p1244_0]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [h1233, hlam, p1244_1]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [h1235, hlam, p1244_1]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [h0, h1229, hc12, hc24, hlam, hphi, p1244_1]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                rcases p1244_3 (m.d 0 1) (by simp) with h1261 | h1261
                                · linarith only [h1261, h2, hlam]
                                · linarith only [h0, h1261, hlam]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                rcases p1244_3 (m.d 0 1) (by simp) with h1264 | h1264
                                · linarith only [h1264, h2, hlam]
                                · linarith only [h1, h1264, hlam]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [hlam, p1244_0]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [h1229, h1238, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1244_1, u5ehi1]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [h1, h1227, h1231, h1240, h1243, hc12, hc34, hlam, hphi, ht23, p1244_1]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                rcases p1244_3 (m.d 0 1) (by simp) with h1270 | h1270
                                · linarith only [h1205, h1270, hlam]
                                · linarith only [h0, h1270, hlam]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                rcases p1244_3 (m.d 0 1) (by simp) with h1273 | h1273
                                · linarith only [h1205, h1273, hlam]
                                · linarith only [h1, h1273, hlam]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [h1237, hlam, p1244_0]
                              · have p1244_0 := h1244c.1
                                have p1244_1 := h1244c.2.1
                                have p1244_2 := h1244c.2.2.1
                                have p1244_3 := h1244c.2.2.2
                                linarith only [hlam, p1244_0]
                            · linarith only [h1, h1227, h1229, h1238, h1243, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h1229, h1237, h1242, hlam]
                    · linarith only [h1, h1227, h1237, h2, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_13_25_L_I_L_I_H_R_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2
  · exact r1l7_11_13_25_L_I_L_I_H_R_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2

end R2N4
