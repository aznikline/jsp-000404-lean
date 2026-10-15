import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_70S10

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_14_H_I_L_0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h514 | h514
  · rcases m.htr 0 2 4 (by decide) (by decide) with h515 | h515
    · rcases m.htr 0 2 5 (by decide) (by decide) with h516 | h516
      · rcases m.htr 0 4 5 (by decide) (by decide) with h517 | h517
        · rcases m.htr 1 2 3 (by decide) (by decide) with h518 | h518
          · rcases m.htr 1 2 4 (by decide) (by decide) with h519 | h519
            · rcases m.htr 1 2 5 (by decide) (by decide) with h520 | h520
              · rcases m.htr 2 3 4 (by decide) (by decide) with h521 | h521
                · rcases m.htr 2 3 5 (by decide) (by decide) with h522 | h522
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h523 | h523
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h524 | h524
                      · rcases h2bigk with h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h0, hlam, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h521, h524, hc02, hc45, hlam, hphi, ht0b, ht5b, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h0, h521, h524, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          rcases p525_3 (m.d 0 2) (by simp) with h530 | h530
                          · rcases p525_3 (m.d 1 2) (by simp) with h531 | h531
                            · rcases p525_3 (m.d 2 3) (by simp) with h532 | h532
                              · linarith only [h514, h532, hlam]
                              · linarith only [h522, h532, hlam]
                            · linarith only [h520, h531, hlam]
                          · linarith only [h530, hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h521, h524, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h521, h524, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          rcases p525_3 (m.d 0 2) (by simp) with h541 | h541
                          · linarith only [h0, h541, hlam]
                          · linarith only [h516, h541, hlam]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h514, hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h518, hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h514, h521, h524, hc02, hc45, hlam, hphi, ht0b, ht5b, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h0, h514, h522, h524, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h515, hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h519, hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h521, hlam, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h515, h522, h524, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p525_1, u4elo0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h516, hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h520, hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h522, hlam, p525_1]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [h523, hlam, p525_0]
                        · have p525_0 := h525c.1
                          have p525_1 := h525c.2.1
                          have p525_2 := h525c.2.2.1
                          have p525_3 := h525c.2.2.2
                          linarith only [hlam, p525_0]
                      · linarith only [h517, h524, hc34, hlam, hphi, u4elo0]
                    · linarith only [h517, h523, hc24, hlam, hphi, u4elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h561 | h561
                    · linarith only [h521, h522, h561, hlam]
                    · linarith only [h517, h561, hc24, hlam, hphi, u4elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h564 | h564
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h565 | h565
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h566 | h566
                      · rcases h2bigk with h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h0, hlam, p567_1]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h0, h564, h566, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p567_1]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h0, h521, h564, h566, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p567_1]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          rcases p567_3 (m.d 0 2) (by simp) with h572 | h572
                          · rcases p567_3 (m.d 1 2) (by simp) with h573 | h573
                            · rcases p567_3 (m.d 2 3) (by simp) with h574 | h574
                              · linarith only [h514, h574, hlam]
                              · linarith only [h564, h574, hlam]
                            · linarith only [h520, h573, hlam]
                          · linarith only [h572, hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p567_1]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h564, h566, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p567_1]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h521, h564, h566, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p567_1]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          rcases p567_3 (m.d 0 2) (by simp) with h583 | h583
                          · linarith only [h0, h583, hlam]
                          · linarith only [h516, h583, hlam]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h514, hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h518, hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h521, hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h519, h521, h564, h566, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p567_1, u4elo1]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h515, hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h519, hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h519, hc23, hlam, hphi, ht34, p567_1, u4elo1]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h519, h564, h566, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p567_1, u4elo1]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h516, hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h520, hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h564, hlam, p567_1]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [h565, hlam, p567_0]
                        · have p567_0 := h567c.1
                          have p567_1 := h567c.2.1
                          have p567_2 := h567c.2.2.1
                          have p567_3 := h567c.2.2.2
                          linarith only [hlam, p567_0]
                      · linarith only [h517, h566, hc34, hlam, hphi, u4elo0]
                    · linarith only [h517, h565, hc24, hlam, hphi, u4elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h603 | h603
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h604 | h604
                      · rcases h2bigk with h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [hlam, p605_0]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [h0, hlam, p605_1]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          rcases p605_3 (m.d 0 2) (by simp) with h608 | h608
                          · rcases p605_3 (m.d 1 2) (by simp) with h609 | h609
                            · rcases p605_3 (m.d 2 3) (by simp) with h610 | h610
                              · linarith only [h610, hlam, p605_0]
                              · rcases p605_3 (m.d 2 4) (by simp) with h612 | h612
                                · linarith only [h515, h612, hlam]
                                · linarith only [h521, h612, hlam]
                            · linarith only [h518, h609, hlam]
                          · linarith only [h608, hlam, p605_0]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [h0, h603, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p605_1]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          rcases p605_3 (m.d 0 2) (by simp) with h618 | h618
                          · rcases p605_3 (m.d 1 2) (by simp) with h619 | h619
                            · rcases p605_3 (m.d 2 3) (by simp) with h620 | h620
                              · linarith only [h514, h620, hlam]
                              · rcases p605_3 (m.d 2 4) (by simp) with h622 | h622
                                · linarith only [h515, h622, hlam]
                                · linarith only [h603, h622, hlam]
                            · linarith only [h520, h619, hlam]
                          · linarith only [h618, hlam, p605_0]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p605_1]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [hlam, p605_0]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          rcases p605_3 (m.d 0 2) (by simp) with h629 | h629
                          · linarith only [h0, h629, hlam]
                          · linarith only [h514, h629, hlam]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [h603, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p605_1]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          rcases p605_3 (m.d 0 2) (by simp) with h633 | h633
                          · linarith only [h0, h633, hlam]
                          · linarith only [h516, h633, hlam]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [h514, hlam, p605_0]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [h518, hlam, p605_0]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [hlam, p605_0]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [h521, hlam, p605_0]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [h564, hlam, p605_0]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [h515, hlam, p605_0]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [h519, hlam, p605_0]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [hc23, hlam, hphi, ht34, p605_1, u4elo2]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [hlam, p605_0]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [h515, h564, hc23, hlam, hphi, ht34, p605_1, u4elo0]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [h516, hlam, p605_0]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [h520, hlam, p605_0]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [h516, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p605_1]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [h603, hlam, p605_0]
                        · have p605_0 := h605c.1
                          have p605_1 := h605c.2.1
                          have p605_2 := h605c.2.2.1
                          have p605_3 := h605c.2.2.2
                          linarith only [hlam, p605_0]
                      · linarith only [h517, h521, h604, hc24, hlam, hphi, u4elo0]
                    · linarith only [h517, h603, hc24, hlam, hphi, u4elo0]
              · linarith only [h0, h516, h517, h520, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
            · linarith only [h0, h519, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · linarith only [h0, h514, h518, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h656 | h656
          · rcases m.htr 1 2 4 (by decide) (by decide) with h657 | h657
            · rcases m.htr 1 2 5 (by decide) (by decide) with h658 | h658
              · rcases m.htr 2 3 4 (by decide) (by decide) with h659 | h659
                · rcases m.htr 2 3 5 (by decide) (by decide) with h660 | h660
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h661 | h661
                    · linarith only [h515, h517, h661, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h663 | h663
                      · linarith only [h514, h517, h659, h663, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h2bigk with h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [hlam, p665_0]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [h0, hlam, p665_1]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [h0, h660, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p665_1]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          rcases p665_3 (m.d 0 2) (by simp) with h669 | h669
                          · rcases p665_3 (m.d 1 2) (by simp) with h670 | h670
                            · rcases p665_3 (m.d 2 3) (by simp) with h671 | h671
                              · linarith only [h514, h671, hlam]
                              · linarith only [h659, h671, hlam]
                            · linarith only [h657, h670, hlam]
                          · linarith only [h669, hlam, p665_0]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          rcases p665_3 (m.d 0 2) (by simp) with h676 | h676
                          · rcases p665_3 (m.d 1 2) (by simp) with h677 | h677
                            · rcases p665_3 (m.d 2 3) (by simp) with h678 | h678
                              · linarith only [h514, h678, hlam]
                              · linarith only [h660, h678, hlam]
                            · linarith only [h658, h677, hlam]
                          · linarith only [h676, hlam, p665_0]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p665_1]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [hlam, p665_0]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [h660, h663, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p665_1]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          rcases p665_3 (m.d 0 2) (by simp) with h686 | h686
                          · linarith only [h0, h686, hlam]
                          · linarith only [h515, h686, hlam]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          rcases p665_3 (m.d 0 2) (by simp) with h689 | h689
                          · linarith only [h0, h689, hlam]
                          · linarith only [h516, h689, hlam]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [h514, hlam, p665_0]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [h656, hlam, p665_0]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [hlam, p665_0]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [h514, h659, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p665_1]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [h0, h514, h660, h663, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p665_1]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [h515, hlam, p665_0]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [h657, hlam, p665_0]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [h659, hlam, p665_1]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [hlam, p665_0]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [h661, hlam, p665_1]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [h516, hlam, p665_0]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [h658, hlam, p665_0]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [h660, hlam, p665_1]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [h0, h516, h659, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p665_1]
                        · have p665_0 := h665c.1
                          have p665_1 := h665c.2.1
                          have p665_2 := h665c.2.2.1
                          have p665_3 := h665c.2.2.2
                          linarith only [hlam, p665_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h707 | h707
                    · linarith only [h515, h517, h707, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h709 | h709
                      · linarith only [h516, h517, h659, h660, h709, hlam]
                      · linarith only [h659, h660, h709, hc34, hlam, hphi, u4elo4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h712 | h712
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h713 | h713
                    · linarith only [h515, h517, h713, hlam]
                    · linarith only [h659, h712, h713, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h716 | h716
                    · linarith only [h515, h517, h716, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h718 | h718
                      · linarith only [h517, h718, hc04, hlam, hphi, u4elo3]
                      · linarith only [h659, h718, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h0, h516, h658, hlam]
            · linarith only [h0, h515, h517, h657, hc02, hlam, hphi, ht23, ht34, u4elo4]
          · linarith only [h0, h514, h656, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h724 | h724
        · linarith only [h515, h516, h724, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h726 | h726
          · rcases m.htr 1 2 4 (by decide) (by decide) with h727 | h727
            · rcases m.htr 1 2 5 (by decide) (by decide) with h728 | h728
              · rcases m.htr 2 3 4 (by decide) (by decide) with h729 | h729
                · linarith only [h514, h516, h728, h729, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h731 | h731
                  · linarith only [h515, h516, h728, h729, h731, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h733 | h733
                    · linarith only [h515, h516, h724, h728, h733, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h515, h516, h729, h733, hc23, hlam, hphi, ht34, u4elo4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h736 | h736
                · linarith only [h514, h516, h724, h736, hc34, hlam, hphi, u4elo4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h738 | h738
                  · linarith only [h515, h516, h724, h728, h736, h738, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h740 | h740
                    · linarith only [h515, h516, h724, h740, hlam]
                    · linarith only [h0, h515, h728, h736, h740, hc23, hlam, hphi, ht34, u4elo4]
            · linarith only [h0, h515, h727, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
          · linarith only [h0, h514, h726, hlam]
    · linarith only [h514, h515, hc23, hlam, hphi, ht34, u4elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h746 | h746
    · rcases m.htr 0 2 5 (by decide) (by decide) with h747 | h747
      · rcases m.htr 0 4 5 (by decide) (by decide) with h748 | h748
        · rcases m.htr 1 2 3 (by decide) (by decide) with h749 | h749
          · rcases m.htr 1 2 4 (by decide) (by decide) with h750 | h750
            · rcases m.htr 1 2 5 (by decide) (by decide) with h751 | h751
              · rcases m.htr 2 3 4 (by decide) (by decide) with h752 | h752
                · rcases m.htr 2 3 5 (by decide) (by decide) with h753 | h753
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h754 | h754
                    · linarith only [h514, h746, h749, h754, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h748, h754, hc24, hlam, hphi, u4elo0]
                  · linarith only [h514, h747, h753, hlam]
                · linarith only [h514, h752, hc02, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h514, h747, h749, h751, hlam]
            · linarith only [h514, h746, h749, h750, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h761 | h761
            · rcases m.htr 1 2 5 (by decide) (by decide) with h762 | h762
              · rcases m.htr 2 3 4 (by decide) (by decide) with h763 | h763
                · rcases m.htr 2 3 5 (by decide) (by decide) with h764 | h764
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h765 | h765
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h766 | h766
                      · rcases h2bigk with h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c | h767c
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [hlam, p767_0]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h0, hlam, p767_1]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h514, hlam, p767_0]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h763, h766, hc02, hc45, hlam, hphi, ht0b, ht5b, p767_1]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h0, h749, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p767_1]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h749, hc02, hc23, hlam, hphi, p767_1]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [hlam, p767_0]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h749, hlam, p767_0]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h749, h763, h766, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p767_1]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h749, h764, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p767_1]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h746, h763, h766, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p767_1]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p767_1]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [hlam, p767_0]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h763, h766, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p767_1]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          rcases p767_3 (m.d 0 2) (by simp) with h782 | h782
                          · linarith only [h514, h782, hlam]
                          · linarith only [h747, h782, hlam]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h746, hlam, p767_0]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h761, hlam, p767_0]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h763, hlam, p767_1]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [hlam, p767_0]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h746, h764, h766, hc02, hc45, hlam, hphi, ht0b, ht5b, p767_1]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h747, hlam, p767_0]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h762, hlam, p767_0]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h764, hlam, p767_1]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [h765, hlam, p767_0]
                        · have p767_0 := h767c.1
                          have p767_1 := h767c.2.1
                          have p767_2 := h767c.2.2.1
                          have p767_3 := h767c.2.2.2
                          linarith only [hlam, p767_0]
                      · linarith only [h748, h766, hc34, hlam, hphi, u4elo0]
                    · linarith only [h748, h765, hc24, hlam, hphi, u4elo0]
                  · linarith only [h0, h749, h764, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h749, h763, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h747, h762, hlam]
            · linarith only [h0, h761, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h801 | h801
          · rcases m.htr 1 2 4 (by decide) (by decide) with h802 | h802
            · rcases m.htr 1 2 5 (by decide) (by decide) with h803 | h803
              · rcases m.htr 2 3 4 (by decide) (by decide) with h804 | h804
                · rcases m.htr 2 3 5 (by decide) (by decide) with h805 | h805
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h806 | h806
                    · linarith only [h514, h746, h801, h806, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h808 | h808
                      · linarith only [h514, h747, h748, h801, h804, h806, h808, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h2bigk with h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h0, hlam, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h514, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h514, h801, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h514, h801, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h0, h514, hc01, hc12, hlam, hphi, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          rcases p810_3 (m.d 0 2) (by simp) with h819 | h819
                          · linarith only [h0, h819, hlam]
                          · linarith only [h746, h819, hlam]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          rcases p810_3 (m.d 0 2) (by simp) with h822 | h822
                          · linarith only [h0, h822, hlam]
                          · linarith only [h747, h822, hlam]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h747, h801, h804, h806, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h801, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h801, h804, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h801, h804, h806, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h746, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h802, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h804, hlam, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h806, hlam, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h747, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h803, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h805, hlam, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h747, h804, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hlam, p810_0]
                  · linarith only [h514, h747, h805, hlam]
                · linarith only [h514, h804, hc02, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h514, h747, h803, hc12, hc23, hlam, hphi]
            · linarith only [h514, h801, h802, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h844 | h844
            · rcases m.htr 1 2 5 (by decide) (by decide) with h845 | h845
              · rcases m.htr 2 3 4 (by decide) (by decide) with h846 | h846
                · rcases m.htr 2 3 5 (by decide) (by decide) with h847 | h847
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h848 | h848
                    · linarith only [h746, h748, h848, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h850 | h850
                      · linarith only [h748, h850, hc04, hlam, hphi, u4elo3]
                      · rcases h2bigk with h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h0, hlam, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h514, hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h0, h801, h846, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h0, h801, h846, h848, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h801, hc02, hc23, hlam, hphi, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h801, hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h801, h846, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h801, h846, h848, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h747, h846, h848, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          rcases p852_3 (m.d 0 2) (by simp) with h866 | h866
                          · linarith only [h514, h866, hlam]
                          · linarith only [h746, h866, hlam]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          rcases p852_3 (m.d 0 2) (by simp) with h869 | h869
                          · linarith only [h514, h869, hlam]
                          · linarith only [h747, h869, hlam]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h746, hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h844, hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h846, hlam, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h848, hlam, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h747, hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h845, hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h847, hlam, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h747, h846, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [hlam, p852_0]
                  · linarith only [h0, h801, h847, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h801, h846, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h747, h845, hlam]
            · linarith only [h0, h746, h844, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h886 | h886
        · linarith only [h746, h747, h886, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h888 | h888
          · rcases m.htr 1 2 4 (by decide) (by decide) with h889 | h889
            · rcases m.htr 1 2 5 (by decide) (by decide) with h890 | h890
              · rcases m.htr 2 3 4 (by decide) (by decide) with h891 | h891
                · rcases m.htr 2 3 5 (by decide) (by decide) with h892 | h892
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h893 | h893
                    · linarith only [h746, h747, h886, h888, h892, h893, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h746, h747, h891, h893, hc34, hlam, hphi, u4elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h896 | h896
                    · linarith only [h514, h746, h892, h896, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h514, h746, h891, h892, h896, hc34, hlam, hphi, u4elo4]
                · linarith only [h0, h514, h891, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h514, h746, h888, h890, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h514, h746, h888, h889, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h902 | h902
            · rcases m.htr 1 2 5 (by decide) (by decide) with h903 | h903
              · linarith only [h746, h747, h888, h903, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h905 | h905
                · rcases m.htr 2 3 5 (by decide) (by decide) with h906 | h906
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h907 | h907
                    · linarith only [h746, h886, h907, hlam]
                    · linarith only [h0, h903, h907, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h0, h888, h906, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h888, h905, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h0, h746, h902, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h913 | h913
      · rcases m.htr 0 4 5 (by decide) (by decide) with h914 | h914
        · rcases m.htr 1 2 3 (by decide) (by decide) with h915 | h915
          · rcases m.htr 1 2 4 (by decide) (by decide) with h916 | h916
            · rcases m.htr 1 2 5 (by decide) (by decide) with h917 | h917
              · rcases m.htr 2 3 4 (by decide) (by decide) with h918 | h918
                · rcases m.htr 2 3 5 (by decide) (by decide) with h919 | h919
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h920 | h920
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h921 | h921
                      · rcases h2bigk with h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [hlam, p922_0]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h0, hlam, p922_1]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h514, hlam, p922_0]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h746, hlam, p922_0]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h746, h916, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p922_1, u4elo1]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p922_1]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [hlam, p922_0]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h918, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p922_1]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h746, h913, h919, h921, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p922_1]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          rcases p922_3 (m.d 0 2) (by simp) with h932 | h932
                          · linarith only [h0, h932, hlam]
                          · linarith only [h913, h932, hlam]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h913, h915, h919, h921, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p922_1]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h915, hlam, p922_0]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [hlam, p922_0]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h746, h913, h915, h919, h921, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p922_1]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h915, h919, h921, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p922_1]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h913, h916, h919, h921, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p922_1, u4elo1]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h916, hlam, p922_0]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h918, hlam, p922_1]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [hlam, p922_0]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h916, h919, h921, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p922_1, u4elo1]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h913, hlam, p922_0]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h917, hlam, p922_0]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h919, hlam, p922_1]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [h920, hlam, p922_0]
                        · have p922_0 := h922c.1
                          have p922_1 := h922c.2.1
                          have p922_2 := h922c.2.2.1
                          have p922_3 := h922c.2.2.2
                          linarith only [hlam, p922_0]
                      · linarith only [h746, h914, h916, h921, hc34, hlam, hphi, u4elo1]
                    · linarith only [h746, h913, h914, h920, hlam]
                  · linarith only [h514, h746, h913, h916, h919, hc03, hlam, hphi, ht34, u4elo1]
                · linarith only [h514, h918, hc02, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h514, h913, h917, hc12, hc23, hlam, hphi]
            · linarith only [h514, h915, h916, hc02, hlam, hphi, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h956 | h956
            · linarith only [h746, h913, h915, h956, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · linarith only [h0, h956, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · linarith only [h746, h913, h914, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h960 | h960
        · rcases m.htr 1 2 3 (by decide) (by decide) with h961 | h961
          · rcases m.htr 1 2 4 (by decide) (by decide) with h962 | h962
            · rcases m.htr 1 2 5 (by decide) (by decide) with h963 | h963
              · rcases m.htr 2 3 4 (by decide) (by decide) with h964 | h964
                · rcases m.htr 2 3 5 (by decide) (by decide) with h965 | h965
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h966 | h966
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h967 | h967
                      · rcases h2bigk with h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h0, hlam, p968_1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h514, hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h746, hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h913, hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p968_1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h964, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p968_1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h0, h746, hc01, hc12, hlam, hphi, p968_1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h0, h913, hc01, hc12, hlam, hphi, p968_1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p968_1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h961, hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h0, h746, h961, hc01, hc12, hlam, hphi, p968_1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h0, h913, h961, hc01, hc12, hlam, hphi, p968_1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p968_1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h962, hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h964, hlam, p968_1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h0, h913, h962, hc01, hlam, hphi, ht12, ht23, ht34, p968_1, u4elo1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h0, h963, hc01, hc15, hlam, hphi, p968_1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h963, hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h965, hlam, p968_1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h966, hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [hlam, p968_0]
                      · linarith only [h960, h967, hc34, hlam, hphi, u4elo0]
                    · linarith only [h746, h960, h966, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h996 | h996
                    · linarith only [h964, h965, h996, hlam]
                    · linarith only [h746, h960, h996, hlam]
                · linarith only [h0, h514, h964, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h514, h961, h963, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h514, h961, h962, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1002 | h1002
            · linarith only [h0, h1002, h746, h961, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h1002, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1005 | h1005
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1006 | h1006
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1007 | h1007
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1008 | h1008
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1009 | h1009
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1010 | h1010
                    · linarith only [h1006, h1010, h960, hc04, hlam, hphi, u4elo1]
                    · linarith only [h0, h1010, h746, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1013 | h1013
                    · linarith only [h0, h1013, h746, h960, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h0, h1013, h746, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h0, h1008, h514, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h1005, h1007, h514, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h1005, h1006, h514, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1019 | h1019
            · linarith only [h0, h1005, h1019, h746, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h1019, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

theorem r1l7_22_14_H_I_L_0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_22_14_H_I_L_0_x0 m hb2 hb4 h0
  · exact r1l7_22_14_H_I_L_0_x1 m hb2 hb4 h0

end R2N4
