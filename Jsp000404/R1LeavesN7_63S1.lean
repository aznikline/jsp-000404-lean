import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3024000 in
theorem r1l7_10_12_23_L_0_L_I_M_LI_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h508 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h509 | h509
  · rcases m.htr 0 2 4 (by decide) (by decide) with h510 | h510
    · rcases m.htr 0 2 5 (by decide) (by decide) with h511 | h511
      · rcases m.htr 0 3 4 (by decide) (by decide) with h512 | h512
        · rcases m.htr 0 3 5 (by decide) (by decide) with h513 | h513
          · rcases m.htr 1 2 3 (by decide) (by decide) with h514 | h514
            · rcases m.htr 1 2 4 (by decide) (by decide) with h515 | h515
              · rcases m.htr 1 2 5 (by decide) (by decide) with h516 | h516
                · rcases m.htr 1 3 4 (by decide) (by decide) with h517 | h517
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h518 | h518
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h519 | h519
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h520 | h520
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h521 | h521
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h522 | h522
                            · linarith only [h508, h514, h519, h522, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h510, h521, h522, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h525 | h525
                            · linarith only [h512, h521, h525, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · rcases h2bigk with h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h0, hlam, p527_1]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h520, hc35, hlam, hphi, ht0b, ht5b, p527_1, u0elo1]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                rcases p527_3 (m.d 0 2) (by simp) with h531 | h531
                                · rcases p527_3 (m.d 1 2) (by simp) with h532 | h532
                                  · rcases p527_3 (m.d 2 3) (by simp) with h533 | h533
                                    · linarith only [h509, h533, hlam]
                                    · linarith only [h519, h533, hlam]
                                  · linarith only [h515, h532, hlam]
                                · linarith only [h531, hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                rcases p527_3 (m.d 0 2) (by simp) with h538 | h538
                                · rcases p527_3 (m.d 1 2) (by simp) with h539 | h539
                                  · rcases p527_3 (m.d 2 3) (by simp) with h540 | h540
                                    · linarith only [h509, h540, hlam]
                                    · linarith only [h520, h540, hlam]
                                  · linarith only [h516, h539, hlam]
                                · linarith only [h538, hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h509, h520, h525, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p527_1]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                rcases p527_3 (m.d 0 2) (by simp) with h547 | h547
                                · linarith only [h0, h547, hlam]
                                · linarith only [h509, h547, hlam]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                rcases p527_3 (m.d 0 2) (by simp) with h550 | h550
                                · linarith only [h0, h550, hlam]
                                · linarith only [h510, h550, hlam]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                rcases p527_3 (m.d 0 2) (by simp) with h553 | h553
                                · linarith only [h0, h553, hlam]
                                · linarith only [h511, h553, hlam]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h509, hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h514, hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h508, h514, hc24, hlam, hphi, ht0b, ht45, ht5b, p527_1, u0elo0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h0, h508, h514, h519, h521, hc34, hlam, hphi, ht0b, ht45, ht5b, p527_1, u0elo1]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h510, hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h515, hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h519, hlam, p527_1]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h521, hlam, p527_1]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h511, hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h516, hlam, p527_0]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h520, hlam, p527_1]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [h511, h519, hc34, hlam, hphi, ht0b, ht45, ht5b, p527_1, u0elo1]
                              · have p527_0 := h527c.1
                                have p527_1 := h527c.2.1
                                have p527_2 := h527c.2.2.1
                                have p527_3 := h527c.2.2.2
                                linarith only [hlam, p527_0]
                        · linarith only [h513, h520, hc23, hlam, hphi, u3elo0]
                      · linarith only [h512, h519, hc23, hlam, hphi, u3elo0]
                    · linarith only [h513, h518, hc13, hlam, hphi, u3elo0]
                  · linarith only [h512, h514, h517, hc23, hlam, hphi, u3elo0]
                · linarith only [h0, h511, h516, hlam]
              · linarith only [h0, h510, h515, hlam]
            · linarith only [h0, h514, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h578 | h578
            · rcases m.htr 1 2 4 (by decide) (by decide) with h579 | h579
              · rcases m.htr 1 2 5 (by decide) (by decide) with h580 | h580
                · rcases m.htr 1 3 4 (by decide) (by decide) with h581 | h581
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h582 | h582
                    · linarith only [h508, h513, h582, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h584 | h584
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h585 | h585
                        · linarith only [h513, h585, hc03, hlam, hphi, u3elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h587 | h587
                          · linarith only [h584, h585, h587, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h589 | h589
                            · linarith only [h508, h578, h584, h587, h589, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · rcases h2bigk with h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h0, hlam, p591_1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h584, hc34, hlam, hphi, ht0b, ht45, ht5b, p591_1, u0elo1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                rcases p591_3 (m.d 0 2) (by simp) with h595 | h595
                                · rcases p591_3 (m.d 1 2) (by simp) with h596 | h596
                                  · rcases p591_3 (m.d 2 3) (by simp) with h597 | h597
                                    · linarith only [h509, h597, hlam]
                                    · linarith only [h584, h597, hlam]
                                  · linarith only [h579, h596, hlam]
                                · linarith only [h595, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h584, h585, hc34, hlam, hphi, ht0b, ht45, ht5b, p591_1, u0elo1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h509, h584, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p591_1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                rcases p591_3 (m.d 0 2) (by simp) with h605 | h605
                                · linarith only [h0, h605, hlam]
                                · linarith only [h509, h605, hlam]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                rcases p591_3 (m.d 0 2) (by simp) with h608 | h608
                                · linarith only [h0, h608, hlam]
                                · linarith only [h510, h608, hlam]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                rcases p591_3 (m.d 0 2) (by simp) with h611 | h611
                                · linarith only [h0, h611, hlam]
                                · linarith only [h511, h611, hlam]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h509, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h578, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h508, h578, hc24, hlam, hphi, ht0b, ht45, ht5b, p591_1, u0elo0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h585, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h510, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h579, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h584, hlam, p591_1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h587, hlam, p591_1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h511, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h580, hlam, p591_0]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h511, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p591_1, u0elo1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [h511, h584, hc34, hlam, hphi, ht0b, ht45, ht5b, p591_1, u0elo1]
                              · have p591_0 := h591c.1
                                have p591_1 := h591c.2.1
                                have p591_2 := h591c.2.2.1
                                have p591_3 := h591c.2.2.2
                                linarith only [hlam, p591_0]
                      · linarith only [h512, h513, h584, hc23, hlam, hphi, u3elo4]
                  · linarith only [h512, h513, h581, hc13, hlam, hphi, u3elo4]
                · linarith only [h0, h511, h580, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h510, h579, hlam]
            · linarith only [h0, h578, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h634 | h634
          · rcases m.htr 1 2 3 (by decide) (by decide) with h635 | h635
            · rcases m.htr 1 2 4 (by decide) (by decide) with h636 | h636
              · rcases m.htr 1 2 5 (by decide) (by decide) with h637 | h637
                · rcases m.htr 1 3 4 (by decide) (by decide) with h638 | h638
                  · linarith only [h508, h512, h638, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h640 | h640
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h641 | h641
                      · linarith only [h508, h512, h640, h641, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h643 | h643
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h644 | h644
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h645 | h645
                            · rcases h2bigk with h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h0, hlam, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h643, h645, hc45, hlam, hphi, ht0b, ht5b, p646_1, u0elo1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h641, h643, h645, hc45, hlam, hphi, ht0b, ht5b, p646_1, u0elo1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                rcases p646_3 (m.d 0 2) (by simp) with h651 | h651
                                · rcases p646_3 (m.d 1 2) (by simp) with h652 | h652
                                  · rcases p646_3 (m.d 2 3) (by simp) with h653 | h653
                                    · linarith only [h509, h653, hlam]
                                    · linarith only [h643, h653, hlam]
                                  · linarith only [h637, h652, hlam]
                                · linarith only [h651, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h0, h508, h635, h643, h645, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                rcases p646_3 (m.d 0 2) (by simp) with h660 | h660
                                · linarith only [h0, h660, hlam]
                                · linarith only [h509, h660, hlam]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                rcases p646_3 (m.d 0 2) (by simp) with h663 | h663
                                · linarith only [h0, h663, hlam]
                                · linarith only [h510, h663, hlam]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                rcases p646_3 (m.d 0 2) (by simp) with h666 | h666
                                · linarith only [h0, h666, hlam]
                                · linarith only [h511, h666, hlam]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h509, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h635, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h641, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h508, h635, hc25, hlam, hphi, ht0b, ht5b, p646_1, u0elo0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h510, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h636, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h510, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p646_1, u0elo1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h510, h643, h645, hc45, hlam, hphi, ht0b, ht5b, p646_1, u0elo1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h511, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h637, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h643, hlam, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h644, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [hlam, p646_0]
                            · linarith only [h510, h512, h644, h645, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h641, h643, h644, hlam]
                        · linarith only [h512, h634, h643, hc23, hlam, hphi, u3elo3]
                    · linarith only [h512, h634, h640, hc13, hlam, hphi, u3elo3]
                · linarith only [h0, h511, h637, hlam]
              · linarith only [h0, h508, h510, h635, h636, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
            · linarith only [h0, h635, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h691 | h691
            · rcases m.htr 1 2 4 (by decide) (by decide) with h692 | h692
              · rcases m.htr 1 2 5 (by decide) (by decide) with h693 | h693
                · rcases m.htr 1 3 4 (by decide) (by decide) with h694 | h694
                  · linarith only [h508, h512, h694, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h696 | h696
                    · linarith only [h508, h634, h696, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h698 | h698
                      · linarith only [h508, h512, h691, h698, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h700 | h700
                        · linarith only [h508, h634, h691, h700, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h702 | h702
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h703 | h703
                            · rcases h2bigk with h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c | h704c
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [hlam, p704_0]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [h0, hlam, p704_1]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                rcases p704_3 (m.d 0 2) (by simp) with h707 | h707
                                · rcases p704_3 (m.d 1 2) (by simp) with h708 | h708
                                  · rcases p704_3 (m.d 2 3) (by simp) with h709 | h709
                                    · linarith only [h709, hlam, p704_0]
                                    · rcases p704_3 (m.d 2 4) (by simp) with h711 | h711
                                      · linarith only [h510, h711, hlam]
                                      · linarith only [h698, h711, hlam]
                                  · linarith only [h691, h708, hlam]
                                · linarith only [h707, hlam, p704_0]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [h702, hc45, hlam, hphi, ht0b, ht5b, p704_1, u0elo1]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                rcases p704_3 (m.d 0 2) (by simp) with h717 | h717
                                · rcases p704_3 (m.d 1 2) (by simp) with h718 | h718
                                  · rcases p704_3 (m.d 2 3) (by simp) with h719 | h719
                                    · linarith only [h509, h719, hlam]
                                    · rcases p704_3 (m.d 2 4) (by simp) with h721 | h721
                                      · linarith only [h510, h721, hlam]
                                      · linarith only [h702, h721, hlam]
                                  · linarith only [h693, h718, hlam]
                                · linarith only [h717, hlam, p704_0]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [h510, h702, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p704_1]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [hlam, p704_0]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                rcases p704_3 (m.d 0 2) (by simp) with h728 | h728
                                · linarith only [h0, h728, hlam]
                                · linarith only [h509, h728, hlam]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                rcases p704_3 (m.d 0 2) (by simp) with h731 | h731
                                · linarith only [h0, h731, hlam]
                                · linarith only [h510, h731, hlam]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                rcases p704_3 (m.d 0 2) (by simp) with h734 | h734
                                · linarith only [h0, h734, hlam]
                                · linarith only [h511, h734, hlam]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [h509, hlam, p704_0]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [h691, hlam, p704_0]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [hlam, p704_0]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [h698, hlam, p704_0]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [h700, hlam, p704_0]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [h510, hlam, p704_0]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [h692, hlam, p704_0]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [h510, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p704_1, u0elo1]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [hlam, p704_0]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [h510, h512, h700, hc23, hlam, hphi, p704_1, u3elo3]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [h511, hlam, p704_0]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [h693, hlam, p704_0]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [h511, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p704_1, u0elo1]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [h702, hlam, p704_0]
                              · have p704_0 := h704c.1
                                have p704_1 := h704c.2.1
                                have p704_2 := h704c.2.2.1
                                have p704_3 := h704c.2.2.2
                                linarith only [hlam, p704_0]
                            · linarith only [h510, h512, h702, h703, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h753 | h753
                            · linarith only [h698, h702, h753, hc23, hlam, hphi, u3elo3]
                            · rcases h2bigk with h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h0, hlam, p755_1]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                rcases p755_3 (m.d 0 2) (by simp) with h758 | h758
                                · rcases p755_3 (m.d 1 2) (by simp) with h759 | h759
                                  · rcases p755_3 (m.d 2 3) (by simp) with h760 | h760
                                    · linarith only [h760, hlam, p755_0]
                                    · rcases p755_3 (m.d 2 4) (by simp) with h762 | h762
                                      · linarith only [h510, h762, hlam]
                                      · linarith only [h698, h762, hlam]
                                  · linarith only [h691, h759, hlam]
                                · linarith only [h758, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                rcases p755_3 (m.d 0 2) (by simp) with h767 | h767
                                · rcases p755_3 (m.d 1 2) (by simp) with h768 | h768
                                  · rcases p755_3 (m.d 2 3) (by simp) with h769 | h769
                                    · linarith only [h509, h769, hlam]
                                    · rcases p755_3 (m.d 2 4) (by simp) with h771 | h771
                                      · linarith only [h771, hlam, p755_0]
                                      · rcases p755_3 (m.d 2 5) (by simp) with h773 | h773
                                        · linarith only [h511, h773, hlam]
                                        · linarith only [h702, h773, hlam]
                                  · linarith only [h692, h768, hlam]
                                · linarith only [h767, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                rcases p755_3 (m.d 0 2) (by simp) with h778 | h778
                                · rcases p755_3 (m.d 1 2) (by simp) with h779 | h779
                                  · rcases p755_3 (m.d 2 3) (by simp) with h780 | h780
                                    · linarith only [h509, h780, hlam]
                                    · rcases p755_3 (m.d 2 4) (by simp) with h782 | h782
                                      · linarith only [h510, h782, hlam]
                                      · rcases p755_3 (m.d 2 5) (by simp) with h784 | h784
                                        · linarith only [h784, hlam, p755_0]
                                        · rcases h2emin with h786 | h786 | h786 | h786 | h786
                                          · rcases h3bigk with h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [hlam, p787_0]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [h691, hc23, hlam, hphi, p787_1, u3elo0]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [hc23, hlam, hphi, p787_1, u3elo0]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [h512, hlam, p787_0]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [h634, hlam, p787_0]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [h508, hlam, p787_0]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [hlam, p787_0]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [hc23, hlam, hphi, p787_1, u3elo1]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [h694, hlam, p787_0]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [h696, hlam, p787_0]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [h509, hlam, p787_0]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [h691, hlam, p787_0]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [hlam, p787_0]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [h698, hlam, p787_0]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [h700, hlam, p787_0]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [h753, hc03, hc45, hlam, hphi, ht34, p787_1]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [h691, h753, hc23, hc45, hlam, hphi, ht34, p787_1]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [h753, hc23, hc45, hlam, hphi, ht34, p787_1]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [hlam, p787_0]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [h753, hlam, p787_1]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [h508, h691, hc23, hlam, hphi, p787_1, u3elo4]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [h691, hc23, hlam, hphi, p787_1, u3elo4]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [hc23, hlam, hphi, p787_1, u3elo4]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [h508, h512, h691, hc23, hlam, hphi, p787_1, u3elo4]
                                            · have p787_0 := h787c.1
                                              have p787_1 := h787c.2.1
                                              have p787_2 := h787c.2.2.1
                                              have p787_3 := h787c.2.2.2
                                              linarith only [hlam, p787_0]
                                          · rcases h3bigk with h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [hlam, p813_0]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [h512, h691, hc23, hlam, hphi, p813_1, u3elo3]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [h512, hc23, hlam, hphi, p813_1, u3elo3]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [h512, hlam, p813_0]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [h634, hlam, p813_0]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [h508, hlam, p813_0]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [hlam, p813_0]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [h508, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p813_1, u0elo0]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [h694, hlam, p813_0]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [h696, hlam, p813_0]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [h509, hlam, p813_0]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [h691, hlam, p813_0]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [hlam, p813_0]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [h698, hlam, p813_0]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [h700, hlam, p813_0]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [hc03, hlam, hphi, p813_1, u3elo3]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [h691, hc23, hlam, hphi, p813_1, u3elo3]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [hc23, hlam, hphi, p813_1, u3elo3]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [hlam, p813_0]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [h753, hlam, p813_1]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [h508, h691, hc23, hlam, hphi, p813_1, u3elo4]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [h691, hc23, hlam, hphi, p813_1, u3elo4]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [hc23, hlam, hphi, p813_1, u3elo4]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [h508, h512, h691, hc23, hlam, hphi, p813_1, u3elo4]
                                            · have p813_0 := h813c.1
                                              have p813_1 := h813c.2.1
                                              have p813_2 := h813c.2.2.1
                                              have p813_3 := h813c.2.2.2
                                              linarith only [hlam, p813_0]
                                          · linarith only [h508, h691, h786, hlam, ht23, u3elo0]
                                          · linarith only [h510, h786, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                                          · linarith only [h786, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1, u0elo1]
                                  · linarith only [h693, h779, hlam]
                                · linarith only [h778, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                rcases p755_3 (m.d 0 2) (by simp) with h844 | h844
                                · linarith only [h0, h844, hlam]
                                · rcases p755_3 (m.d 1 2) (by simp) with h846 | h846
                                  · rcases p755_3 (m.d 2 3) (by simp) with h847 | h847
                                    · linarith only [h691, h847, hlam]
                                    · rcases p755_3 (m.d 2 4) (by simp) with h849 | h849
                                      · linarith only [h692, h849, hlam]
                                      · rcases p755_3 (m.d 2 5) (by simp) with h851 | h851
                                        · linarith only [h693, h851, hlam]
                                        · rcases h2emin with h853 | h853 | h853 | h853 | h853
                                          · linarith only [h853, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p755_1]
                                          · rcases h3bigk with h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [hlam, p855_0]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h512, h753, hc13, hc45, hlam, hphi, ht34, p855_1]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h512, h753, hc23, hc45, hlam, hphi, ht34, p855_1]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h512, hlam, p855_0]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h634, hlam, p855_0]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h508, hlam, p855_0]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [hlam, p855_0]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [hc23, hlam, hphi, p855_1, u3elo1]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h694, hlam, p855_0]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h696, hlam, p855_0]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h509, hlam, p855_0]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h691, hlam, p855_0]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [hlam, p855_0]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h698, hlam, p855_0]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h700, hlam, p855_0]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h753, hc03, hc45, hlam, hphi, ht34, p855_1]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h691, h753, hc23, hc45, hlam, hphi, ht34, p855_1]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h753, hc23, hc45, hlam, hphi, ht34, p855_1]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [hlam, p855_0]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h753, hlam, p855_1]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h508, h691, hc23, hlam, hphi, p855_1, u3elo4]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h691, hc23, hlam, hphi, p855_1, u3elo4]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [hc23, hlam, hphi, p855_1, u3elo4]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [h508, h512, h691, hc23, hlam, hphi, p855_1, u3elo4]
                                            · have p855_0 := h855c.1
                                              have p855_1 := h855c.2.1
                                              have p855_2 := h855c.2.2.1
                                              have p855_3 := h855c.2.2.2
                                              linarith only [hlam, p855_0]
                                          · linarith only [h508, h691, h853, hlam, ht23, u3elo0]
                                          · linarith only [h511, h702, h853, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p755_1]
                                          · linarith only [h511, h853, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p755_1]
                                  · linarith only [h0, h846, hlam]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                rcases p755_3 (m.d 0 2) (by simp) with h886 | h886
                                · linarith only [h0, h886, hlam]
                                · linarith only [h509, h886, hlam]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                rcases p755_3 (m.d 0 2) (by simp) with h889 | h889
                                · linarith only [h0, h889, hlam]
                                · linarith only [h510, h889, hlam]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                rcases p755_3 (m.d 0 2) (by simp) with h892 | h892
                                · linarith only [h0, h892, hlam]
                                · linarith only [h511, h892, hlam]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h509, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h691, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h698, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h700, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h510, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h692, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h511, h702, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p755_1, u0elo1]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h702, hlam, p755_1]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h511, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h693, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h511, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p755_1, u0elo1]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h511, hc24, hlam, hphi, ht0b, ht45, ht5b, p755_1, u0elo1]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [hlam, p755_0]
                · linarith only [h0, h508, h511, h691, h693, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h510, h692, hlam]
            · linarith only [h0, h691, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h913 | h913
        · rcases m.htr 0 3 5 (by decide) (by decide) with h914 | h914
          · linarith only [h0, h508, h511, h914, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h916 | h916
            · rcases m.htr 1 2 4 (by decide) (by decide) with h917 | h917
              · rcases m.htr 1 2 5 (by decide) (by decide) with h918 | h918
                · rcases m.htr 1 3 4 (by decide) (by decide) with h919 | h919
                  · linarith only [h0, h508, h511, h918, h919, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h913, h914, h919, hc13, hlam, hphi, u3elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h922 | h922
                  · linarith only [h0, h508, h918, h922, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h913, h914, h916, h922, hc23, hlam, hphi, u3elo4]
              · linarith only [h0, h508, h510, h913, h914, h916, h917, hc23, hlam, hphi, u3elo4]
            · linarith only [h0, h916, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h927 | h927
          · linarith only [h0, h508, h511, h927, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h929 | h929
            · rcases m.htr 1 2 4 (by decide) (by decide) with h930 | h930
              · rcases m.htr 1 2 5 (by decide) (by decide) with h931 | h931
                · rcases m.htr 1 3 4 (by decide) (by decide) with h932 | h932
                  · linarith only [h508, h913, h932, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h934 | h934
                    · linarith only [h0, h508, h511, h927, h934, hlam]
                    · linarith only [h0, h508, h511, h929, h931, h934, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h937 | h937
                  · linarith only [h508, h913, h937, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h939 | h939
                    · linarith only [h0, h508, h931, h939, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h508, h931, h939, hc13, hlam, hphi, u3elo4]
              · linarith only [h0, h508, h510, h929, h930, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h508, h929, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h944 | h944
      · rcases m.htr 0 3 4 (by decide) (by decide) with h945 | h945
        · linarith only [h0, h508, h510, h945, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h947 | h947
          · rcases m.htr 1 2 3 (by decide) (by decide) with h948 | h948
            · rcases m.htr 1 2 4 (by decide) (by decide) with h949 | h949
              · rcases m.htr 1 2 5 (by decide) (by decide) with h950 | h950
                · rcases m.htr 1 3 4 (by decide) (by decide) with h951 | h951
                  · linarith only [h0, h508, h510, h945, h949, h951, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h508, h510, h949, h951, hc13, hlam, hphi, u3elo3]
                · linarith only [h510, h944, h949, h950, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h955 | h955
                · rcases m.htr 1 3 4 (by decide) (by decide) with h956 | h956
                  · linarith only [h0, h508, h949, h956, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h508, h949, h956, hc13, hlam, hphi, u3elo3]
                · linarith only [h0, h508, h944, h948, h955, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h508, h948, hc13, hlam, hphi, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h961 | h961
            · rcases m.htr 1 2 4 (by decide) (by decide) with h962 | h962
              · rcases m.htr 1 2 5 (by decide) (by decide) with h963 | h963
                · rcases m.htr 1 3 4 (by decide) (by decide) with h964 | h964
                  · linarith only [h0, h508, h510, h945, h962, h964, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h508, h510, h962, h964, hc13, hlam, hphi, u3elo3]
                · linarith only [h510, h944, h962, h963, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h968 | h968
                · rcases m.htr 1 3 4 (by decide) (by decide) with h969 | h969
                  · linarith only [h0, h508, h962, h969, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h508, h961, h962, h969, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h508, h944, h961, h968, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
            · linarith only [h0, h961, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h974 | h974
        · linarith only [h0, h508, h510, h974, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h976 | h976
          · linarith only [h0, h508, h944, h974, h976, hc13, hlam, hphi, u3elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h978 | h978
            · rcases m.htr 1 2 4 (by decide) (by decide) with h979 | h979
              · rcases m.htr 1 2 5 (by decide) (by decide) with h980 | h980
                · rcases m.htr 1 3 4 (by decide) (by decide) with h981 | h981
                  · linarith only [h0, h508, h510, h974, h979, h981, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h508, h510, h978, h979, h981, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h508, h510, h978, h979, h980, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h985 | h985
                · linarith only [h0, h508, h944, h978, h979, h985, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h987 | h987
                  · linarith only [h0, h508, h979, h987, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h508, h978, h979, h987, hc23, hlam, hphi, u3elo3]
            · linarith only [h0, h508, h978, hc13, hlam, hphi, u3elo2]
  · linarith only [h0, h508, h509, hc13, hlam, hphi, u3elo2]

end R2N4
