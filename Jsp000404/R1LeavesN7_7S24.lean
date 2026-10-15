import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S16
import Jsp000404.R1LeavesN7_7S23

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11562000 in
set_option maxHeartbeats 11562000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s12 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h10472 | h10472
  · rcases m.htr 0 1 4 (by decide) (by decide) with h10473 | h10473
    · rcases m.htr 0 1 5 (by decide) (by decide) with h10474 | h10474
      · rcases m.htr 0 2 3 (by decide) (by decide) with h10475 | h10475
        · rcases m.htr 0 2 4 (by decide) (by decide) with h10476 | h10476
          · rcases m.htr 0 2 5 (by decide) (by decide) with h10477 | h10477
            · rcases m.htr 0 3 4 (by decide) (by decide) with h10478 | h10478
              · rcases m.htr 0 3 5 (by decide) (by decide) with h10479 | h10479
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10480 | h10480
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10481 | h10481
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10482 | h10482
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10483 | h10483
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10484 | h10484
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10485 | h10485
                            · linarith only [h0, h10472, h10485, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · linarith only [h0, h10472, h10479, h10484, h10485, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10488 | h10488
                            · linarith only [h0, h10472, h10488, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h10490 | h10490
                              · linarith only [h0, h10472, h10478, h10484, h10490, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h10492 | h10492
                                · linarith only [h0, h10472, h10478, h10480, h10481, h10484, h10490, h10492, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h10494 | h10494
                                  · linarith only [h0, h10472, h10478, h10480, h10481, h10484, h10490, h10494, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10496 | h10496
                                    · linarith only [h10482, h10490, h10496, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10498 | h10498
                                      · linarith only [h0, h10472, h10478, h10484, h10490, h10498, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                      · linarith only [h0, h10472, h10478, h10480, h10481, h10484, h10498, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h10472, h10479, h10483, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h10472, h10478, h10480, h10482, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h0, h10472, h10478, h10480, h10481, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10504 | h10504
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10505 | h10505
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10506 | h10506
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10507 | h10507
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10508 | h10508
                            · linarith only [h0, h10472, h10508, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · linarith only [h0, h10472, h10479, h10507, h10508, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10511 | h10511
                            · linarith only [h0, h10472, h10511, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h10513 | h10513
                              · linarith only [h0, h10472, h10478, h10480, h10507, h10513, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h10515 | h10515
                                · linarith only [h10504, h10507, h10515, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h10517 | h10517
                                  · linarith only [h10504, h10511, h10517, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10519 | h10519
                                    · linarith only [h10476, h10478, h10480, h10507, h10519, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10521 | h10521
                                      · linarith only [h10478, h10480, h10521, hlam]
                                      · rcases h1bigk with h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c | h10523c
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [hlam, p10523_0]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [h0, hlam, p10523_0]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          rcases p10523_3 (m.d 0 1) (by simp) with h10526 | h10526
                                          · rcases p10523_3 (m.d 1 2) (by simp) with h10527 | h10527
                                            · rcases p10523_3 (m.d 1 3) (by simp) with h10528 | h10528
                                              · linarith only [h10528, hlam, p10523_0]
                                              · rcases p10523_3 (m.d 1 4) (by simp) with h10530 | h10530
                                                · linarith only [h10473, h10530, hlam]
                                                · linarith only [h10507, h10530, hlam]
                                            · linarith only [h10504, h10527, hlam]
                                          · linarith only [h10526, hlam, p10523_0]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          rcases p10523_3 (m.d 0 1) (by simp) with h10535 | h10535
                                          · rcases p10523_3 (m.d 1 2) (by simp) with h10536 | h10536
                                            · rcases p10523_3 (m.d 1 3) (by simp) with h10537 | h10537
                                              · linarith only [h10472, h10537, hlam]
                                              · rcases p10523_3 (m.d 1 4) (by simp) with h10539 | h10539
                                                · linarith only [h10539, hlam, p10523_0]
                                                · rcases p10523_3 (m.d 1 5) (by simp) with h10541 | h10541
                                                  · linarith only [h10474, h10541, hlam]
                                                  · linarith only [h10513, h10541, hlam]
                                            · linarith only [h10505, h10536, hlam]
                                          · linarith only [h10535, hlam, p10523_0]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [h0, h10506, hc12, hlam, hphi, ht01, ht0b, ht5b, p10523_1, u5ehi2]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [h10474, h10506, hc12, hlam, hphi, ht01, ht0b, ht5b, p10523_1, u5ehi2]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [hlam, p10523_0]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [h0, h10472, h10479, h10507, h10521, hlam, p10523_2]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          rcases p10523_3 (m.d 0 1) (by simp) with h10550 | h10550
                                          · linarith only [h0, h10550, hlam]
                                          · linarith only [h10473, h10550, hlam]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          rcases p10523_3 (m.d 0 1) (by simp) with h10553 | h10553
                                          · linarith only [h0, h10553, hlam]
                                          · linarith only [h10474, h10553, hlam]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [h10472, hlam, p10523_0]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [h10504, hlam, p10523_1]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [hlam, p10523_0]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [h10507, hlam, p10523_1]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [h10511, hlam, p10523_1]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [h10473, hlam, p10523_0]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [h10505, hlam, p10523_1]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [h0, h10473, h10504, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10523_1]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [hlam, p10523_0]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [h10513, hlam, p10523_1]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [h10474, hlam, p10523_0]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [h10506, hlam, p10523_1]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [h0, h10474, h10504, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10523_1]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [h0, h10472, h10479, h10505, h10511, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10523_1]
                                        · have p10523_0 := h10523c.1
                                          have p10523_1 := h10523c.2.1
                                          have p10523_2 := h10523c.2.2.1
                                          have p10523_3 := h10523c.2.2.2
                                          linarith only [hlam, p10523_0]
                        · linarith only [h0, h10474, h10506, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h10472, h10479, h10505, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h10472, h10479, h10504, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10574 | h10574
                  · linarith only [h10478, h10479, h10574, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10576 | h10576
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10577 | h10577
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10578 | h10578
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10579 | h10579
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10580 | h10580
                            · linarith only [h0, h10472, h10479, h10580, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h10582 | h10582
                              · linarith only [h10473, h10574, h10582, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h10584 | h10584
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h10585 | h10585
                                  · linarith only [h10472, h10479, h10576, h10585, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10587 | h10587
                                    · linarith only [h10473, h10574, h10577, h10587, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10589 | h10589
                                      · linarith only [h0, h10474, h10574, h10576, h10580, h10584, h10589, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                      · rcases h1bigk with h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c | h10591c
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [hlam, p10591_0]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [h0, hlam, p10591_0]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [h0, h10579, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10591_1]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          rcases p10591_3 (m.d 0 1) (by simp) with h10595 | h10595
                                          · rcases p10591_3 (m.d 1 2) (by simp) with h10596 | h10596
                                            · rcases p10591_3 (m.d 1 3) (by simp) with h10597 | h10597
                                              · linarith only [h10472, h10597, hlam]
                                              · linarith only [h10579, h10597, hlam]
                                            · linarith only [h10577, h10596, hlam]
                                          · linarith only [h10595, hlam, p10591_0]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [h0, h10576, h10580, h10584, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10591_1]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [h10472, h10576, h10584, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10591_1]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [hlam, p10591_0]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          rcases p10591_3 (m.d 0 1) (by simp) with h10605 | h10605
                                          · linarith only [h0, h10605, hlam]
                                          · linarith only [h10472, h10605, hlam]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          rcases p10591_3 (m.d 0 1) (by simp) with h10608 | h10608
                                          · linarith only [h0, h10608, hlam]
                                          · linarith only [h10473, h10608, hlam]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          rcases p10591_3 (m.d 0 1) (by simp) with h10611 | h10611
                                          · linarith only [h0, h10611, hlam]
                                          · linarith only [h10474, h10611, hlam]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [h10472, hlam, p10591_0]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [h10576, hlam, p10591_1]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [hlam, p10591_0]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [h10472, h10479, h10589, hc14, hc45, hlam, hphi, p10591_1]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [h10580, hlam, p10591_1]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [h10473, hlam, p10591_0]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [h10577, hlam, p10591_1]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [h10579, hlam, p10591_0]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [hlam, p10591_0]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [h10582, hlam, p10591_1]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [h10474, hlam, p10591_0]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [h10578, hlam, p10591_1]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [h0, h10474, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10591_1]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [h0, h10474, h10577, h10584, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10591_1]
                                        · have p10591_0 := h10591c.1
                                          have p10591_1 := h10591c.2.1
                                          have p10591_2 := h10591c.2.2.1
                                          have p10591_3 := h10591c.2.2.2
                                          linarith only [hlam, p10591_0]
                                · linarith only [h10478, h10479, h10584, hc23, hc35, hlam, hphi]
                          · linarith only [h10478, h10479, h10579, hc13, hc35, hlam, hphi]
                        · linarith only [h0, h10474, h10578, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h10474, h10577, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h10474, h10576, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h10634 | h10634
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10635 | h10635
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10636 | h10636
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10637 | h10637
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10638 | h10638
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10639 | h10639
                          · linarith only [h10478, h10634, h10639, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10641 | h10641
                            · linarith only [h0, h10473, h10639, h10641, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · linarith only [h10478, h10634, h10636, h10641, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h10474, h10638, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h10474, h10637, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h10474, h10636, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h10478, h10634, h10635, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10648 | h10648
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10649 | h10649
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10650 | h10650
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10651 | h10651
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10652 | h10652
                          · linarith only [h10472, h10478, h10648, h10652, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10654 | h10654
                            · linarith only [h10472, h10634, h10654, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h10656 | h10656
                              · linarith only [h0, h10473, h10656, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h10658 | h10658
                                · linarith only [h10478, h10648, h10649, h10652, h10656, h10658, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h10660 | h10660
                                  · linarith only [h0, h10473, h10634, h10648, h10649, h10652, h10656, h10660, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10662 | h10662
                                    · linarith only [h10650, h10656, h10662, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10664 | h10664
                                      · rcases h1bigk with h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c | h10665c
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [hlam, p10665_0]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [h0, hlam, p10665_0]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          rcases p10665_3 (m.d 0 1) (by simp) with h10668 | h10668
                                          · rcases p10665_3 (m.d 1 2) (by simp) with h10669 | h10669
                                            · rcases p10665_3 (m.d 1 3) (by simp) with h10670 | h10670
                                              · linarith only [h10670, hlam, p10665_0]
                                              · rcases p10665_3 (m.d 1 4) (by simp) with h10672 | h10672
                                                · linarith only [h10473, h10672, hlam]
                                                · linarith only [h10652, h10672, hlam]
                                            · linarith only [h10649, h10669, hlam]
                                          · linarith only [h10668, hlam, p10665_0]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          rcases p10665_3 (m.d 0 1) (by simp) with h10677 | h10677
                                          · rcases p10665_3 (m.d 1 2) (by simp) with h10678 | h10678
                                            · rcases p10665_3 (m.d 1 3) (by simp) with h10679 | h10679
                                              · linarith only [h10472, h10679, hlam]
                                              · rcases p10665_3 (m.d 1 4) (by simp) with h10681 | h10681
                                                · linarith only [h10681, hlam, p10665_0]
                                                · rcases p10665_3 (m.d 1 5) (by simp) with h10683 | h10683
                                                  · linarith only [h10474, h10683, hlam]
                                                  · linarith only [h10656, h10683, hlam]
                                            · linarith only [h10650, h10678, hlam]
                                          · linarith only [h10677, hlam, p10665_0]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [h0, h10651, hc12, hlam, hphi, ht01, ht0b, ht5b, p10665_1, u5ehi2]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [h10473, h10648, h10649, h10652, h10656, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10665_1]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [hlam, p10665_0]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [h0, h10473, h10648, h10652, h10656, hlam, p10665_2]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [h0, h10473, h10648, h10656, hlam, p10665_2]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          rcases p10665_3 (m.d 0 1) (by simp) with h10693 | h10693
                                          · linarith only [h0, h10693, hlam]
                                          · linarith only [h10474, h10693, hlam]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [h10472, hlam, p10665_0]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [h10649, hlam, p10665_1]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [hlam, p10665_0]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [h10652, hlam, p10665_1]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [h10654, hlam, p10665_1]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [h10473, hlam, p10665_0]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [h10650, hlam, p10665_1]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [h10473, h10648, h10649, h10656, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10665_1]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [hlam, p10665_0]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [h10656, hlam, p10665_1]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [h10474, hlam, p10665_0]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [h10651, hlam, p10665_1]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [h0, h10474, h10649, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10665_1]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [h0, h10473, h10648, h10656, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p10665_1]
                                        · have p10665_0 := h10665c.1
                                          have p10665_1 := h10665c.2.1
                                          have p10665_2 := h10665c.2.2.1
                                          have p10665_3 := h10665c.2.2.2
                                          linarith only [hlam, p10665_0]
                                      · linarith only [h10478, h10648, h10664, hlam]
                        · linarith only [h0, h10473, h10648, h10651, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h0, h10473, h10648, h10650, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h0, h10473, h10648, h10649, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10715 | h10715
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10716 | h10716
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10717 | h10717
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10718 | h10718
                          · linarith only [h10472, h10478, h10718, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10720 | h10720
                            · linarith only [h0, h10472, h10634, h10720, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h10722 | h10722
                              · linarith only [h0, h10473, h10478, h10648, h10722, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h10724 | h10724
                                · linarith only [h10472, h10478, h10715, h10724, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h10726 | h10726
                                  · linarith only [h10472, h10634, h10715, h10726, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10728 | h10728
                                    · linarith only [h10476, h10648, h10728, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10730 | h10730
                                      · rcases h1bigk with h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c | h10731c
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [hlam, p10731_0]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [h0, hlam, p10731_0]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          rcases p10731_3 (m.d 0 1) (by simp) with h10734 | h10734
                                          · rcases p10731_3 (m.d 1 2) (by simp) with h10735 | h10735
                                            · rcases p10731_3 (m.d 1 3) (by simp) with h10736 | h10736
                                              · linarith only [h10736, hlam, p10731_0]
                                              · rcases p10731_3 (m.d 1 4) (by simp) with h10738 | h10738
                                                · linarith only [h10473, h10738, hlam]
                                                · linarith only [h10718, h10738, hlam]
                                            · linarith only [h10715, h10735, hlam]
                                          · linarith only [h10734, hlam, p10731_0]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          rcases p10731_3 (m.d 0 1) (by simp) with h10743 | h10743
                                          · rcases p10731_3 (m.d 1 2) (by simp) with h10744 | h10744
                                            · rcases p10731_3 (m.d 1 3) (by simp) with h10745 | h10745
                                              · linarith only [h10472, h10745, hlam]
                                              · rcases p10731_3 (m.d 1 4) (by simp) with h10747 | h10747
                                                · linarith only [h10747, hlam, p10731_0]
                                                · rcases p10731_3 (m.d 1 5) (by simp) with h10749 | h10749
                                                  · linarith only [h10474, h10749, hlam]
                                                  · linarith only [h10722, h10749, hlam]
                                            · linarith only [h10716, h10744, hlam]
                                          · linarith only [h10743, hlam, p10731_0]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [h0, h10717, hc12, hlam, hphi, ht01, ht0b, ht5b, p10731_1, u5ehi2]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [h10474, h10717, hc12, hlam, hphi, ht01, ht0b, ht5b, p10731_1, u5ehi2]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [hlam, p10731_0]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          rcases p10731_3 (m.d 0 1) (by simp) with h10757 | h10757
                                          · linarith only [h0, h10757, hlam]
                                          · linarith only [h10472, h10757, hlam]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          rcases p10731_3 (m.d 0 1) (by simp) with h10760 | h10760
                                          · linarith only [h0, h10760, hlam]
                                          · linarith only [h10473, h10760, hlam]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          rcases p10731_3 (m.d 0 1) (by simp) with h10763 | h10763
                                          · linarith only [h0, h10763, hlam]
                                          · linarith only [h10474, h10763, hlam]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [h10472, hlam, p10731_0]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [h10715, hlam, p10731_1]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [hlam, p10731_0]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [h10718, hlam, p10731_1]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [h10720, hlam, p10731_1]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [h10473, hlam, p10731_0]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [h10716, hlam, p10731_1]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [h10473, h10648, h10715, h10730, hc23, hc34, hlam, hphi, p10731_1]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [hlam, p10731_0]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [h10722, hlam, p10731_1]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [h10474, hlam, p10731_0]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [h10717, hlam, p10731_1]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [h0, h10474, h10715, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10731_1]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [h0, h10474, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p10731_1]
                                        · have p10731_0 := h10731c.1
                                          have p10731_1 := h10731c.2.1
                                          have p10731_2 := h10731c.2.2.1
                                          have p10731_3 := h10731c.2.2.2
                                          linarith only [hlam, p10731_0]
                                      · rcases h1bigk with h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c | h10781c
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [hlam, p10781_0]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [h0, hlam, p10781_0]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          rcases p10781_3 (m.d 0 1) (by simp) with h10784 | h10784
                                          · rcases p10781_3 (m.d 1 2) (by simp) with h10785 | h10785
                                            · rcases p10781_3 (m.d 1 3) (by simp) with h10786 | h10786
                                              · linarith only [h10786, hlam, p10781_0]
                                              · rcases p10781_3 (m.d 1 4) (by simp) with h10788 | h10788
                                                · linarith only [h10473, h10788, hlam]
                                                · linarith only [h10718, h10788, hlam]
                                            · linarith only [h10715, h10785, hlam]
                                          · linarith only [h10784, hlam, p10781_0]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          rcases p10781_3 (m.d 0 1) (by simp) with h10793 | h10793
                                          · rcases p10781_3 (m.d 1 2) (by simp) with h10794 | h10794
                                            · rcases p10781_3 (m.d 1 3) (by simp) with h10795 | h10795
                                              · linarith only [h10472, h10795, hlam]
                                              · rcases p10781_3 (m.d 1 4) (by simp) with h10797 | h10797
                                                · linarith only [h10797, hlam, p10781_0]
                                                · rcases p10781_3 (m.d 1 5) (by simp) with h10799 | h10799
                                                  · linarith only [h10474, h10799, hlam]
                                                  · linarith only [h10722, h10799, hlam]
                                            · linarith only [h10716, h10794, hlam]
                                          · linarith only [h10793, hlam, p10781_0]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p10781_1, u5ehi1]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [h10474, hc12, hlam, hphi, ht01, ht0b, ht5b, p10781_1, u5ehi1]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [hlam, p10781_0]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          rcases p10781_3 (m.d 0 1) (by simp) with h10807 | h10807
                                          · linarith only [h0, h10807, hlam]
                                          · linarith only [h10472, h10807, hlam]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          rcases p10781_3 (m.d 0 1) (by simp) with h10810 | h10810
                                          · linarith only [h0, h10810, hlam]
                                          · linarith only [h10473, h10810, hlam]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          rcases p10781_3 (m.d 0 1) (by simp) with h10813 | h10813
                                          · linarith only [h0, h10813, hlam]
                                          · linarith only [h10474, h10813, hlam]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [h10472, hlam, p10781_0]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [h10715, hlam, p10781_1]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [hlam, p10781_0]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [h10718, hlam, p10781_1]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [h10720, hlam, p10781_1]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [h10473, hlam, p10781_0]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [h10716, hlam, p10781_1]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [h0, h10473, h10715, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10781_1]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [hlam, p10781_0]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [h10722, hlam, p10781_1]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [h10474, hlam, p10781_0]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [h10717, hlam, p10781_1]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [h0, h10474, h10715, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10781_1]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [h0, h10474, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p10781_1]
                                        · have p10781_0 := h10781c.1
                                          have p10781_1 := h10781c.2.1
                                          have p10781_2 := h10781c.2.2.1
                                          have p10781_3 := h10781c.2.2.2
                                          linarith only [hlam, p10781_0]
                        · linarith only [h0, h10474, h10717, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h10474, h10716, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h10474, h10715, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h0, h10474, h10477, hlam]
          · linarith only [h0, h10473, h10476, hlam]
        · linarith only [h0, h10472, h10475, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h10837 | h10837
        · rcases m.htr 0 2 4 (by decide) (by decide) with h10838 | h10838
          · rcases m.htr 0 2 5 (by decide) (by decide) with h10839 | h10839
            · rcases m.htr 0 3 4 (by decide) (by decide) with h10840 | h10840
              · rcases m.htr 0 3 5 (by decide) (by decide) with h10841 | h10841
                · linarith only [h10472, h10474, h10841, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10843 | h10843
                  · linarith only [h10472, h10474, h10840, h10843, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10845 | h10845
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10846 | h10846
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10847 | h10847
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10848 | h10848
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10849 | h10849
                            · linarith only [h10472, h10474, h10841, h10847, h10849, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h10851 | h10851
                              · linarith only [h10473, h10474, h10843, h10851, hlam]
                              · linarith only [h10472, h10474, h10848, h10851, hc34, hc45, hlam, hphi]
                          · linarith only [h10840, h10841, h10848, hc13, hc35, hlam, hphi]
                        · linarith only [h0, h10473, h10839, h10847, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h10838, h10846, hlam]
                    · linarith only [h0, h10837, h10845, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h10858 | h10858
                · linarith only [h10473, h10474, h10840, h10858, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10860 | h10860
                  · linarith only [h10473, h10474, h10860, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10862 | h10862
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10863 | h10863
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10864 | h10864
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10865 | h10865
                          · linarith only [h10472, h10840, h10865, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10867 | h10867
                            · linarith only [h10472, h10474, h10858, h10867, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h10869 | h10869
                              · linarith only [h10473, h10474, h10840, h10860, h10864, h10869, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h10871 | h10871
                                · linarith only [h10472, h10474, h10862, h10869, h10871, hc34, hc45, hlam, hphi]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h10873 | h10873
                                  · linarith only [h10837, h10858, h10873, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10875 | h10875
                                    · linarith only [h0, h10474, h10838, h10869, h10875, hc01, hc12, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10877 | h10877
                                      · linarith only [h10473, h10474, h10862, h10865, h10869, h10877, hc23, hc34, hlam, hphi]
                                      · rcases h1bigk with h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c | h10879c
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [hlam, p10879_0]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [h0, hlam, p10879_0]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [h10474, h10862, h10867, hc23, hc35, hlam, hphi, p10879_1]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [h10474, h10862, h10865, h10867, hc23, hc35, hlam, hphi, p10879_1]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [h10474, hlam, p10879_0]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          rcases p10879_3 (m.d 0 1) (by simp) with h10885 | h10885
                                          · linarith only [h10885, hlam, p10879_0]
                                          · rcases p10879_3 (m.d 1 2) (by simp) with h10887 | h10887
                                            · rcases p10879_3 (m.d 1 3) (by simp) with h10888 | h10888
                                              · linarith only [h10862, h10888, hlam]
                                              · rcases p10879_3 (m.d 1 4) (by simp) with h10890 | h10890
                                                · linarith only [h10863, h10890, hlam]
                                                · rcases p10879_3 (m.d 1 5) (by simp) with h10892 | h10892
                                                  · linarith only [h10864, h10892, hlam]
                                                  · linarith only [h10474, h10892, hlam]
                                            · linarith only [h10887, hlam, p10879_0]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [hlam, p10879_0]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          rcases p10879_3 (m.d 0 1) (by simp) with h10897 | h10897
                                          · linarith only [h0, h10897, hlam]
                                          · linarith only [h10472, h10897, hlam]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          rcases p10879_3 (m.d 0 1) (by simp) with h10900 | h10900
                                          · linarith only [h0, h10900, hlam]
                                          · linarith only [h10473, h10900, hlam]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [h10474, hc01, hc12, hlam, hphi, p10879_1]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [h10472, hlam, p10879_0]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [h10862, hlam, p10879_1]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [hlam, p10879_0]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [h10865, hlam, p10879_1]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [h10867, hlam, p10879_1]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [h10473, hlam, p10879_0]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [h10863, hlam, p10879_1]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [h10473, h10474, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10879_1]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [hlam, p10879_0]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [h10869, hlam, p10879_1]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [h10472, h10867, hc13, hc35, hlam, hphi, p10879_1]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [h10864, hlam, p10879_1]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          rcases p10879_3 (m.d 0 1) (by simp) with h10916 | h10916
                                          · linarith only [h10474, h10916, hlam]
                                          · linarith only [h10472, h10916, hlam]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          rcases p10879_3 (m.d 0 1) (by simp) with h10919 | h10919
                                          · linarith only [h10474, h10919, hlam]
                                          · linarith only [h10473, h10919, hlam]
                                        · have p10879_0 := h10879c.1
                                          have p10879_1 := h10879c.2.1
                                          have p10879_2 := h10879c.2.2.1
                                          have p10879_3 := h10879c.2.2.2
                                          linarith only [hlam, p10879_0]
                        · linarith only [h0, h10839, h10864, hlam]
                      · linarith only [h0, h10838, h10863, hlam]
                    · linarith only [h0, h10837, h10862, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h10926 | h10926
              · rcases m.htr 0 3 5 (by decide) (by decide) with h10927 | h10927
                · linarith only [h0, h10472, h10839, h10927, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10929 | h10929
                  · linarith only [h0, h10472, h10839, h10926, h10929, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10931 | h10931
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10932 | h10932
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10933 | h10933
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10934 | h10934
                          · linarith only [h0, h10472, h10839, h10933, h10934, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h10472, h10839, h10926, h10931, h10933, h10934, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10937 | h10937
                          · linarith only [h0, h10472, h10933, h10937, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h10472, h10926, h10931, h10933, h10937, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · linarith only [h0, h10473, h10838, h10839, h10932, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h10837, h10931, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h10942 | h10942
                · linarith only [h10473, h10474, h10926, h10942, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10944 | h10944
                  · linarith only [h0, h10473, h10839, h10944, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10946 | h10946
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10947 | h10947
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10948 | h10948
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10949 | h10949
                          · linarith only [h0, h10472, h10839, h10926, h10948, h10949, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10951 | h10951
                            · linarith only [h0, h10472, h10839, h10942, h10951, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h10953 | h10953
                              · linarith only [h0, h10473, h10839, h10944, h10948, h10953, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h10955 | h10955
                                · linarith only [h10837, h10839, h10926, h10948, h10955, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h10957 | h10957
                                  · linarith only [h0, h10472, h10839, h10946, h10948, h10957, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10959 | h10959
                                    · linarith only [h0, h10473, h10839, h10947, h10948, h10953, h10959, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10961 | h10961
                                      · linarith only [h0, h10472, h10839, h10946, h10948, h10953, h10961, hc23, hc34, hlam, hphi]
                                      · rcases h1bigk with h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c | h10963c
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [hlam, p10963_0]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [h0, hlam, p10963_0]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [h0, h10839, h10946, h10948, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10963_1]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [h0, h10839, h10946, h10948, h10949, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10963_1]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [h10474, hlam, p10963_0]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          rcases p10963_3 (m.d 0 1) (by simp) with h10969 | h10969
                                          · linarith only [h10969, hlam, p10963_0]
                                          · rcases p10963_3 (m.d 1 2) (by simp) with h10971 | h10971
                                            · rcases p10963_3 (m.d 1 3) (by simp) with h10972 | h10972
                                              · linarith only [h10946, h10972, hlam]
                                              · rcases p10963_3 (m.d 1 4) (by simp) with h10974 | h10974
                                                · linarith only [h10947, h10974, hlam]
                                                · rcases p10963_3 (m.d 1 5) (by simp) with h10976 | h10976
                                                  · linarith only [h10948, h10976, hlam]
                                                  · linarith only [h10474, h10976, hlam]
                                            · linarith only [h10971, hlam, p10963_0]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [hlam, p10963_0]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [h0, h10472, h10839, h10948, hlam, p10963_2]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [h0, h10473, h10839, h10948, hlam, p10963_2]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [h0, h10473, h10839, h10946, h10948, h10949, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10963_1]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [h10472, hlam, p10963_0]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [h10946, hlam, p10963_1]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [hlam, p10963_0]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [h10949, hlam, p10963_1]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [h10951, hlam, p10963_1]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [h10473, hlam, p10963_0]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [h10947, hlam, p10963_1]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [h0, h10473, h10839, h10946, h10948, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10963_1]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [hlam, p10963_0]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [h10953, hlam, p10963_1]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [h10472, h10946, h10951, hc23, hc35, hlam, hphi, p10963_1]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [h10948, hlam, p10963_1]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          rcases p10963_3 (m.d 0 1) (by simp) with h10996 | h10996
                                          · linarith only [h10474, h10996, hlam]
                                          · linarith only [h10472, h10996, hlam]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          rcases p10963_3 (m.d 0 1) (by simp) with h10999 | h10999
                                          · linarith only [h10474, h10999, hlam]
                                          · linarith only [h10473, h10999, hlam]
                                        · have p10963_0 := h10963c.1
                                          have p10963_1 := h10963c.2.1
                                          have p10963_2 := h10963c.2.2.1
                                          have p10963_3 := h10963c.2.2.2
                                          linarith only [hlam, p10963_0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h11003 | h11003
                          · linarith only [h0, h10472, h10948, h11003, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h11005 | h11005
                            · linarith only [h0, h10473, h11003, h11005, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h11007 | h11007
                              · linarith only [h0, h10473, h10944, h10948, h11007, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h11009 | h11009
                                · linarith only [h10472, h10926, h10946, h11009, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h11011 | h11011
                                  · linarith only [h0, h10473, h10946, h10948, h11003, h11011, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                                  · linarith only [h0, h10473, h10946, h10948, h11003, h11011, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h10472, h10838, h10946, h10947, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h10472, h10837, h10946, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h0, h10473, h10838, hlam]
        · linarith only [h0, h10472, h10837, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h11018 | h11018
      · rcases m.htr 0 2 3 (by decide) (by decide) with h11019 | h11019
        · rcases m.htr 0 2 4 (by decide) (by decide) with h11020 | h11020
          · rcases m.htr 0 2 5 (by decide) (by decide) with h11021 | h11021
            · rcases m.htr 0 3 4 (by decide) (by decide) with h11022 | h11022
              · linarith only [h10472, h10473, h11022, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h11024 | h11024
                · rcases m.htr 0 4 5 (by decide) (by decide) with h11025 | h11025
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h11026 | h11026
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h11027 | h11027
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11028 | h11028
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h11029 | h11029
                          · linarith only [h10472, h11022, h11024, h11029, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h11031 | h11031
                            · linarith only [h10472, h10473, h11029, h11031, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · linarith only [h10472, h10473, h11024, h11029, h11031, hc13, hc34, hlam, hphi]
                        · linarith only [h10473, h11018, h11027, h11028, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h11020, h11027, hlam]
                    · linarith only [h0, h10472, h11024, h11026, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h10473, h11018, h11025, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h11038 | h11038
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h11039 | h11039
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h11040 | h11040
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11041 | h11041
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h11042 | h11042
                          · linarith only [h10472, h10473, h11022, h11040, h11042, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h11044 | h11044
                            · linarith only [h10472, h10473, h11024, h11038, h11042, h11044, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h11046 | h11046
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h11047 | h11047
                                · linarith only [h10473, h11018, h11042, h11047, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h11049 | h11049
                                  · linarith only [h10472, h11024, h11039, h11049, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h11051 | h11051
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h11052 | h11052
                                      · rcases h1bigk with h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c | h11053c
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [hlam, p11053_0]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [h0, hlam, p11053_0]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [h10473, h11042, hc13, hc34, hlam, hphi, p11053_1]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [h10473, hlam, p11053_0]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [h10473, h11041, h11042, h11051, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11053_1, u5ehi4]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [h11018, h11041, h11051, hc12, hlam, hphi, ht01, ht0b, ht5b, p11053_1, u5ehi4]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [hlam, p11053_0]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          rcases p11053_3 (m.d 0 1) (by simp) with h11061 | h11061
                                          · linarith only [h0, h11061, hlam]
                                          · linarith only [h10472, h11061, hlam]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [h10473, h11018, h11041, h11051, hc12, hlam, hphi, ht01, ht0b, ht5b, p11053_1, u5ehi4]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          rcases p11053_3 (m.d 0 1) (by simp) with h11065 | h11065
                                          · linarith only [h0, h11065, hlam]
                                          · linarith only [h11018, h11065, hlam]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [h10472, hlam, p11053_0]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [h11039, hlam, p11053_1]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [hlam, p11053_0]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [h11042, hlam, p11053_1]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [h11044, hlam, p11053_1]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [h11018, h11041, h11051, hc14, hlam, hphi, ht01, ht0b, ht5b, p11053_1, u5ehi4]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [h11040, hlam, p11053_1]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          rcases p11053_3 (m.d 0 1) (by simp) with h11075 | h11075
                                          · linarith only [h10473, h11075, hlam]
                                          · linarith only [h10472, h11075, hlam]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [hlam, p11053_0]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          rcases p11053_3 (m.d 0 1) (by simp) with h11079 | h11079
                                          · linarith only [h10473, h11079, hlam]
                                          · linarith only [h11018, h11079, hlam]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [h11018, hlam, p11053_0]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [h11041, hlam, p11053_1]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [h0, h11018, h11039, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11053_1]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [h11046, hlam, p11053_0]
                                        · have p11053_0 := h11053c.1
                                          have p11053_1 := h11053c.2.1
                                          have p11053_2 := h11053c.2.2.1
                                          have p11053_3 := h11053c.2.2.2
                                          linarith only [hlam, p11053_0]
                                      · linarith only [h10473, h11018, h11041, h11042, h11051, h11052, hlam]
                                    · linarith only [h10473, h11018, h11042, h11046, h11047, h11051, hc23, hc34, hlam, hphi]
                              · linarith only [h10473, h11018, h11046, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                        · linarith only [h10473, h11018, h11040, h11041, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h11018, h11040, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h11018, h11039, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h10473, h11018, h11038, hlam]
            · linarith only [h10473, h11018, h11020, h11021, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h11095 | h11095
            · rcases m.htr 0 3 4 (by decide) (by decide) with h11096 | h11096
              · linarith only [h0, h10472, h11020, h11096, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h11098 | h11098
                · rcases m.htr 0 4 5 (by decide) (by decide) with h11099 | h11099
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h11100 | h11100
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h11101 | h11101
                      · linarith only [h0, h10472, h11020, h11098, h11101, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · linarith only [h0, h10472, h11098, h11101, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h10472, h11098, h11100, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h10472, h11020, h11098, h11099, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h11106 | h11106
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h11107 | h11107
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h11108 | h11108
                      · linarith only [h0, h11018, h11020, h11108, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                      · linarith only [h0, h11018, h11108, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h11018, h11107, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h11018, h11020, h11106, hlam]
            · linarith only [h0, h11018, h11095, hlam]
        · linarith only [h0, h10472, h11019, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h11115 | h11115
        · rcases m.htr 0 2 4 (by decide) (by decide) with h11116 | h11116
          · rcases m.htr 0 2 5 (by decide) (by decide) with h11117 | h11117
            · rcases m.htr 0 3 4 (by decide) (by decide) with h11118 | h11118
              · linarith only [h10472, h10473, h11118, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h11120 | h11120
                · linarith only [h10472, h11018, h11120, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h11122 | h11122
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h11123 | h11123
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h11124 | h11124
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11125 | h11125
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h11126 | h11126
                          · linarith only [h10472, h10473, h11118, h11124, h11126, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h11128 | h11128
                            · linarith only [h10472, h11018, h11120, h11128, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h11130 | h11130
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h11131 | h11131
                                · linarith only [h10472, h11018, h11115, h11126, h11130, h11131, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h11133 | h11133
                                  · linarith only [h10472, h11018, h11123, h11128, h11133, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h11135 | h11135
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h11136 | h11136
                                      · rcases h1bigk with h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [hlam, p11137_0]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [h0, hlam, p11137_0]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [h11018, h11123, h11126, h11130, hc23, hc34, hlam, hphi, p11137_1]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [h10473, hlam, p11137_0]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [h11018, hlam, p11137_0]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          rcases p11137_3 (m.d 0 1) (by simp) with h11143 | h11143
                                          · linarith only [h11143, hlam, p11137_0]
                                          · rcases p11137_3 (m.d 1 2) (by simp) with h11145 | h11145
                                            · rcases p11137_3 (m.d 1 3) (by simp) with h11146 | h11146
                                              · linarith only [h11123, h11146, hlam]
                                              · rcases p11137_3 (m.d 1 4) (by simp) with h11148 | h11148
                                                · linarith only [h11124, h11148, hlam]
                                                · linarith only [h10473, h11148, hlam]
                                            · linarith only [h11145, hlam, p11137_0]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [hlam, p11137_0]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          rcases p11137_3 (m.d 0 1) (by simp) with h11153 | h11153
                                          · linarith only [h0, h11153, hlam]
                                          · linarith only [h10472, h11153, hlam]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [h10473, hc01, hc12, hlam, hphi, p11137_1]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [h10472, h11018, h11123, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11137_1]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [h10472, hlam, p11137_0]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [h11123, hlam, p11137_1]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [hlam, p11137_0]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [h11126, hlam, p11137_1]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [h11128, hlam, p11137_1]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [h10472, h11123, h11126, hc23, hc34, hlam, hphi, p11137_1]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [h11124, hlam, p11137_1]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          rcases p11137_3 (m.d 0 1) (by simp) with h11165 | h11165
                                          · linarith only [h10473, h11165, hlam]
                                          · linarith only [h10472, h11165, hlam]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [hlam, p11137_0]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [h10472, h11018, h11123, h11126, hc23, hc34, hlam, hphi, p11137_1]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [h10472, h11123, h11128, hc23, hc35, hlam, hphi, p11137_1]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [h11125, hlam, p11137_1]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          rcases p11137_3 (m.d 0 1) (by simp) with h11172 | h11172
                                          · linarith only [h11018, h11172, hlam]
                                          · linarith only [h10472, h11172, hlam]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [h11130, hlam, p11137_0]
                                        · have p11137_0 := h11137c.1
                                          have p11137_1 := h11137c.2.1
                                          have p11137_2 := h11137c.2.2.1
                                          have p11137_3 := h11137c.2.2.2
                                          linarith only [hlam, p11137_0]
                                      · linarith only [h10472, h10473, h11116, h11123, h11126, h11135, h11136, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h11178 | h11178
                                      · rcases h1bigk with h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c | h11179c
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [hlam, p11179_0]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [h0, hlam, p11179_0]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [h10473, h11123, h11126, hc23, hc34, hlam, hphi, p11179_1]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [h10473, hlam, p11179_0]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [h11018, hlam, p11179_0]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          rcases p11179_3 (m.d 0 1) (by simp) with h11185 | h11185
                                          · linarith only [h11185, hlam, p11179_0]
                                          · rcases p11179_3 (m.d 1 2) (by simp) with h11187 | h11187
                                            · rcases p11179_3 (m.d 1 3) (by simp) with h11188 | h11188
                                              · linarith only [h11123, h11188, hlam]
                                              · rcases p11179_3 (m.d 1 4) (by simp) with h11190 | h11190
                                                · linarith only [h11124, h11190, hlam]
                                                · linarith only [h10473, h11190, hlam]
                                            · linarith only [h11187, hlam, p11179_0]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [hlam, p11179_0]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          rcases p11179_3 (m.d 0 1) (by simp) with h11195 | h11195
                                          · linarith only [h0, h11195, hlam]
                                          · linarith only [h10472, h11195, hlam]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [h10473, h11122, h11135, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11179_1]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [h11018, hc01, hc12, hlam, hphi, p11179_1]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [h10472, hlam, p11179_0]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [h11123, hlam, p11179_1]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [hlam, p11179_0]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [h11126, hlam, p11179_1]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [h11128, hlam, p11179_1]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [h10472, h11123, h11126, hc23, hc34, hlam, hphi, p11179_1]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [h11124, hlam, p11179_1]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          rcases p11179_3 (m.d 0 1) (by simp) with h11207 | h11207
                                          · linarith only [h10473, h11207, hlam]
                                          · linarith only [h10472, h11207, hlam]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [hlam, p11179_0]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [h10472, h11018, h11123, h11126, hc23, hc34, hlam, hphi, p11179_1]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [h10472, h11123, h11128, hc23, hc35, hlam, hphi, p11179_1]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [h11125, hlam, p11179_1]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          rcases p11179_3 (m.d 0 1) (by simp) with h11214 | h11214
                                          · linarith only [h11018, h11214, hlam]
                                          · linarith only [h10472, h11214, hlam]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [h11130, hlam, p11179_0]
                                        · have p11179_0 := h11179c.1
                                          have p11179_1 := h11179c.2.1
                                          have p11179_2 := h11179c.2.2.1
                                          have p11179_3 := h11179c.2.2.2
                                          linarith only [hlam, p11179_0]
                                      · linarith only [h10472, h10473, h11122, h11126, h11178, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · linarith only [h10472, h10473, h11123, h11130, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h11116, h11117, h11122, h11125, hlam]
                      · linarith only [h0, h11116, h11124, hlam]
                    · linarith only [h0, h11115, h11123, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h11224 | h11224
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h11225 | h11225
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11226 | h11226
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h11227 | h11227
                          · linarith only [h10472, h10473, h11118, h11227, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h11229 | h11229
                            · linarith only [h10472, h10473, h11122, h11229, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h11231 | h11231
                              · linarith only [h10472, h10473, h11122, h11227, h11231, hc13, hc34, hlam, hphi]
                              · linarith only [h10472, h10473, h11224, h11231, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h10472, h10473, h11117, h11224, h11225, h11226, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h11116, h11225, hlam]
                    · linarith only [h0, h11115, h11224, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h11237 | h11237
              · linarith only [h10472, h10473, h11237, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h11239 | h11239
                · linarith only [h0, h10472, h11117, h11239, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h11241 | h11241
                  · linarith only [h11116, h11117, h11241, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h11243 | h11243
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h11244 | h11244
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11245 | h11245
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h11246 | h11246
                          · linarith only [h10472, h10473, h11116, h11117, h11237, h11245, h11246, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h11248 | h11248
                            · linarith only [h10472, h10473, h11116, h11117, h11239, h11248, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h11250 | h11250
                              · linarith only [h10472, h10473, h11241, h11246, h11250, hc13, hc34, hlam, hphi]
                              · linarith only [h10472, h10473, h11243, h11250, hc23, hc45, hlam, hphi, ht34]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h11253 | h11253
                          · linarith only [h0, h10472, h11245, h11253, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h11255 | h11255
                            · linarith only [h10472, h10473, h11244, h11245, h11255, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h11257 | h11257
                              · linarith only [h10472, h10473, h11241, h11243, h11244, h11245, h11257, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                              · linarith only [h10472, h10473, h11243, h11257, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h10472, h11116, h11243, h11244, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h10472, h11115, h11243, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h11262 | h11262
            · rcases m.htr 0 3 4 (by decide) (by decide) with h11263 | h11263
              · linarith only [h0, h10472, h11116, h11263, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h11265 | h11265
                · linarith only [h10472, h11018, h11265, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h11267 | h11267
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h11268 | h11268
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h11269 | h11269
                      · linarith only [h11116, h11262, h11269, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11271 | h11271
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h11272 | h11272
                          · linarith only [h0, h10472, h11263, h11269, h11272, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h11274 | h11274
                            · linarith only [h10472, h11018, h11265, h11274, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h11276 | h11276
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h11277 | h11277
                                · linarith only [h10472, h11018, h11115, h11116, h11269, h11271, h11272, h11277, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · linarith only [h10472, h11018, h11268, h11269, h11271, h11277, hc23, hc34, hlam, hphi]
                              · linarith only [h10472, h11018, h11268, h11269, h11271, h11276, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h11262, h11271, hlam]
                    · linarith only [h0, h11115, h11268, hlam]
                  · linarith only [h11116, h11262, h11267, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h11284 | h11284
              · linarith only [h0, h10472, h11116, h11284, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h11286 | h11286
                · linarith only [h10472, h11018, h11286, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h11288 | h11288
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h11289 | h11289
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h11290 | h11290
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11291 | h11291
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h11292 | h11292
                          · linarith only [h0, h10472, h11116, h11284, h11290, h11292, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h11294 | h11294
                            · linarith only [h0, h10472, h11262, h11286, h11294, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h11296 | h11296
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h11297 | h11297
                                · linarith only [h11115, h11262, h11291, h11292, h11296, h11297, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h11299 | h11299
                                  · linarith only [h0, h10472, h11262, h11289, h11291, h11294, h11299, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h11301 | h11301
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h11302 | h11302
                                      · rcases h1bigk with h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [hlam, p11303_0]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [h0, hlam, p11303_0]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [h0, h11262, h11290, h11301, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11303_1]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [h10473, hlam, p11303_0]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [h11018, hlam, p11303_0]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          rcases p11303_3 (m.d 0 1) (by simp) with h11309 | h11309
                                          · linarith only [h11309, hlam, p11303_0]
                                          · rcases p11303_3 (m.d 1 2) (by simp) with h11311 | h11311
                                            · rcases p11303_3 (m.d 1 3) (by simp) with h11312 | h11312
                                              · linarith only [h11289, h11312, hlam]
                                              · rcases p11303_3 (m.d 1 4) (by simp) with h11314 | h11314
                                                · linarith only [h11290, h11314, hlam]
                                                · linarith only [h10473, h11314, hlam]
                                            · linarith only [h11311, hlam, p11303_0]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [hlam, p11303_0]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [h0, h10472, h11262, h11290, h11301, hlam, p11303_2]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [h0, h11262, h11291, h11296, hc01, hc12, hlam, hphi, p11303_1]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [h0, h10472, h11262, h11289, h11291, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11303_1]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [h10472, hlam, p11303_0]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [h11289, hlam, p11303_1]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [hlam, p11303_0]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [h11292, hlam, p11303_1]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [h11294, hlam, p11303_1]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [h10472, h11289, h11292, hc23, hc34, hlam, hphi, p11303_1]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [h11290, hlam, p11303_1]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          rcases p11303_3 (m.d 0 1) (by simp) with h11329 | h11329
                                          · linarith only [h10473, h11329, hlam]
                                          · linarith only [h10472, h11329, hlam]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [hlam, p11303_0]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [h0, h10472, h11262, h11289, h11291, h11292, hc23, hc34, hlam, hphi, p11303_1]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [h10472, h11289, h11294, hc23, hc35, hlam, hphi, p11303_1]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [h11291, hlam, p11303_1]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          rcases p11303_3 (m.d 0 1) (by simp) with h11336 | h11336
                                          · linarith only [h11018, h11336, hlam]
                                          · linarith only [h10472, h11336, hlam]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [h11296, hlam, p11303_0]
                                        · have p11303_0 := h11303c.1
                                          have p11303_1 := h11303c.2.1
                                          have p11303_2 := h11303c.2.2.1
                                          have p11303_3 := h11303c.2.2.2
                                          linarith only [hlam, p11303_0]
                                      · linarith only [h10472, h10473, h11288, h11289, h11292, h11302, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                    · linarith only [h11116, h11288, h11301, hlam]
                              · linarith only [h10472, h10473, h11288, h11289, h11296, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h10472, h11116, h11289, h11290, h11291, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11345 | h11345
                        · linarith only [h0, h10472, h11262, h11289, h11290, h11345, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h11347 | h11347
                          · linarith only [h0, h10472, h11284, h11290, h11347, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h11349 | h11349
                            · linarith only [h0, h10472, h11290, h11349, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h11351 | h11351
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h11352 | h11352
                                · linarith only [h0, h10472, h11289, h11345, h11347, h11351, h11352, hlam]
                                · linarith only [h0, h10472, h11289, h11290, h11352, hc23, hc34, hlam, hphi]
                              · linarith only [h10472, h10473, h11288, h11289, h11351, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h10472, h11115, h11289, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h11357 | h11357
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h11358 | h11358
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11359 | h11359
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h11360 | h11360
                          · linarith only [h0, h10472, h11116, h11358, h11360, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h11362 | h11362
                            · linarith only [h0, h10472, h11116, h11358, h11362, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h11364 | h11364
                              · linarith only [h10472, h10473, h11288, h11360, h11364, hc13, hc34, hlam, hphi]
                              · linarith only [h10472, h10473, h11357, h11364, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h11116, h11358, h11359, hc02, hc25, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11368 | h11368
                        · linarith only [h0, h10472, h11262, h11357, h11358, h11368, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h11370 | h11370
                          · linarith only [h0, h10472, h11358, h11370, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h11372 | h11372
                            · linarith only [h0, h10472, h11358, h11372, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h11374 | h11374
                              · linarith only [h0, h10472, h11116, h11288, h11357, h11370, h11374, hc23, hc34, hlam, hphi]
                              · linarith only [h10472, h10473, h11357, h11374, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h10472, h11115, h11116, h11357, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h0, h10472, h11115, hlam]
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s13 m hb1 hb3 hb5 h0 h10472

set_option maxHeartbeats 32506000 in
set_option maxHeartbeats 32506000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s0 m hb1 hb3 hb5 h0
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s12 m hb1 hb3 hb5 h0

end R2N4
