import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S25
import Jsp000404.R1LeavesN7_4S26

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10168000 in
set_option maxHeartbeats 10168000 in
theorem r1l7_11_23_L_I_H_I_s13_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h13812 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h13813 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  rcases m.htr 0 2 4 (by decide) (by decide) with h14481 | h14481
  · rcases m.htr 0 3 4 (by decide) (by decide) with h14482 | h14482
    · rcases m.htr 0 3 5 (by decide) (by decide) with h14483 | h14483
      · rcases m.htr 0 4 5 (by decide) (by decide) with h14484 | h14484
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14485 | h14485
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14486 | h14486
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14487 | h14487
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14488 | h14488
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14489 | h14489
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14490 | h14490
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14491 | h14491
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14492 | h14492
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14493 | h14493
                          · linarith only [h13813, h14481, h14485, h14493, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h13813, h14481, h14484, h14485, h14493, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h12794, h13812, h13813, h14481, h14483, h14492, hc03, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h12794, h13812, h13813, h14481, h14482, h14491, hc03, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h12794, h13812, h14481, h14484, h14487, h14490, hc02, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h11385, h14483, h14489, hlam]
                · linarith only [h13813, h14481, h14482, h14485, h14488, hlam]
              · linarith only [h13813, h14485, h14487, hc02, hc25, hlam, hphi]
            · linarith only [h13813, h14481, h14485, h14486, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14503 | h14503
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14504 | h14504
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14505 | h14505
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14506 | h14506
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14507 | h14507
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14508 | h14508
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14509 | h14509
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14510 | h14510
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14511 | h14511
                            · rcases h1bigk with h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c | h14512c
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [hlam, p14512_0]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [h0, hlam, p14512_0]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [h11385, hlam, p14512_0]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [h12794, hlam, p14512_0]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [h12794, h14485, h14503, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p14512_1]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [h14485, hc01, hc23, hlam, hphi, ht12, p14512_1]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [hlam, p14512_0]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [h14485, hlam, p14512_0]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [h12794, h14485, hc01, hc23, hlam, hphi, ht12, p14512_1]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                rcases p14512_3 (m.d 0 1) (by simp) with h14522 | h14522
                                · linarith only [h0, h14522, hlam]
                                · linarith only [h13812, h14522, hlam]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                rcases p14512_3 (m.d 0 1) (by simp) with h14525 | h14525
                                · linarith only [h14525, hlam, p14512_0]
                                · rcases p14512_3 (m.d 1 2) (by simp) with h14527 | h14527
                                  · linarith only [h14485, h14527, hlam]
                                  · linarith only [h0, h14527, hlam]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [h0, h13812, h14485, h14504, h14509, h14511, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14512_1]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [hlam, p14512_0]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [h12794, h13812, h14485, h14504, h14509, h14511, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14512_1]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                rcases p14512_3 (m.d 0 1) (by simp) with h14533 | h14533
                                · linarith only [h11385, h14533, hlam]
                                · linarith only [h13812, h14533, hlam]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [h13812, h14485, h14503, h14504, h14509, h14511, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14512_1]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [h14503, hlam, p14512_1]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [h14505, hlam, p14512_0]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [hlam, p14512_0]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                rcases p14512_3 (m.d 0 1) (by simp) with h14540 | h14540
                                · linarith only [h12794, h14540, hlam]
                                · linarith only [h13812, h14540, hlam]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [h13812, hlam, p14512_0]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [h14504, hlam, p14512_1]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [h14506, hlam, p14512_0]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [h14507, hlam, p14512_0]
                              · have p14512_0 := h14512c.1
                                have p14512_1 := h14512c.2.1
                                have p14512_2 := h14512c.2.2.1
                                have p14512_3 := h14512c.2.2.2
                                linarith only [hlam, p14512_0]
                            · linarith only [h0, h13812, h14485, h14507, h14511, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h12794, h13812, h14485, h14503, h14507, h14510, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h12794, h14485, h14503, h14509, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h12794, h13812, h14485, h14503, h14507, h14508, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h12794, h14484, h14507, hlam]
                  · linarith only [h11385, h14483, h14506, hlam]
                · linarith only [h0, h13812, h14482, h14485, h14504, h14505, hc03, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h12794, h13812, h14503, h14504, hlam]
            · linarith only [h0, h14481, h14503, hlam]
        · linarith only [h12794, h13812, h14484, hlam]
      · linarith only [h11385, h13812, h14483, hlam]
    · linarith only [h13813, h14481, h14482, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h14560 | h14560
    · rcases m.htr 0 3 5 (by decide) (by decide) with h14561 | h14561
      · rcases m.htr 0 4 5 (by decide) (by decide) with h14562 | h14562
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14563 | h14563
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14564 | h14564
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14565 | h14565
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14566 | h14566
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14567 | h14567
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14568 | h14568
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14569 | h14569
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14570 | h14570
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14571 | h14571
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14572 | h14572
                            · rcases h1bigk with h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [hlam, p14573_0]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [h0, hlam, p14573_0]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [h11385, hlam, p14573_0]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [h12794, hlam, p14573_0]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [h0, h14481, h14563, h14565, h14569, h14570, h14572, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14573_1]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                rcases p14573_3 (m.d 0 1) (by simp) with h14579 | h14579
                                · linarith only [h14579, hlam, p14573_0]
                                · rcases p14573_3 (m.d 1 2) (by simp) with h14581 | h14581
                                  · rcases p14573_3 (m.d 1 3) (by simp) with h14582 | h14582
                                    · linarith only [h14563, h14582, hlam]
                                    · linarith only [h11385, h14582, hlam]
                                  · linarith only [h14581, hlam, p14573_0]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [hlam, p14573_0]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [h0, h14481, h14564, h14566, hc01, hc12, hlam, hphi, p14573_1]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [h0, h13812, h14481, h14564, h14565, h14570, h14572, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14573_1]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [h0, h13812, h13813, h14563, hlam, p14573_2]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                rcases p14573_3 (m.d 0 1) (by simp) with h14590 | h14590
                                · linarith only [h14590, hlam, p14573_0]
                                · rcases p14573_3 (m.d 1 2) (by simp) with h14592 | h14592
                                  · rcases p14573_3 (m.d 1 3) (by simp) with h14593 | h14593
                                    · rcases p14573_3 (m.d 1 4) (by simp) with h14594 | h14594
                                      · linarith only [h14566, h14594, hlam]
                                      · linarith only [h12794, h14594, hlam]
                                    · linarith only [h14593, hlam, p14573_0]
                                  · linarith only [h0, h14592, hlam]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [h14563, hlam, p14573_1]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [hlam, p14573_0]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [h0, h13812, h14481, h14564, h14565, h14570, h14572, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p14573_1]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                rcases p14573_3 (m.d 0 1) (by simp) with h14602 | h14602
                                · linarith only [h11385, h14602, hlam]
                                · linarith only [h13812, h14602, hlam]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                rcases p14573_3 (m.d 0 1) (by simp) with h14605 | h14605
                                · linarith only [h14605, hlam, p14573_0]
                                · rcases p14573_3 (m.d 1 2) (by simp) with h14607 | h14607
                                  · rcases p14573_3 (m.d 1 3) (by simp) with h14608 | h14608
                                    · rcases p14573_3 (m.d 1 4) (by simp) with h14609 | h14609
                                      · rcases p14573_3 (m.d 1 5) (by simp) with h14610 | h14610
                                        · linarith only [h14568, h14610, hlam]
                                        · rcases h3bigk with h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [hlam, p14612_0]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h11385, hlam, p14612_1]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h13813, hlam, p14612_1]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h14572, hc03, hc45, hlam, hphi, ht0b, ht5b, p14612_1]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h13813, h14563, h14572, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14612_1]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h11385, h13812, h14565, h14570, h14572, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p14612_1]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [hlam, p14612_0]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h0, h13812, h13813, h14563, h14565, h14570, h14572, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14612_1]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h14563, h14572, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14612_1]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            rcases p14612_3 (m.d 0 3) (by simp) with h14622 | h14622
                                            · linarith only [h11385, h14622, hlam]
                                            · linarith only [h14561, h14622, hlam]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h14560, h14572, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14612_1]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h14563, hlam, p14612_0]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [hlam, p14612_0]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h14563, h14572, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14612_1]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h14563, h14572, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14612_1]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h14560, hlam, p14612_0]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h14566, hlam, p14612_0]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h14569, hlam, p14612_0]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [hlam, p14612_0]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h14560, h14572, hc03, hc45, hlam, hphi, ht0b, ht5b, p14612_1]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h14561, hlam, p14612_0]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h14567, hlam, p14612_0]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h14570, hlam, p14612_0]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [h14572, hlam, p14612_0]
                                          · have p14612_0 := h14612c.1
                                            have p14612_1 := h14612c.2.1
                                            have p14612_2 := h14612c.2.2.1
                                            have p14612_3 := h14612c.2.2.2
                                            linarith only [hlam, p14612_0]
                                      · linarith only [h14609, hlam, p14573_0]
                                    · linarith only [h11385, h14608, hlam]
                                  · linarith only [h0, h14607, hlam]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [h14564, hlam, p14573_1]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [h14566, hlam, p14573_0]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [hlam, p14573_0]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                rcases p14573_3 (m.d 0 1) (by simp) with h14646 | h14646
                                · linarith only [h12794, h14646, hlam]
                                · linarith only [h13812, h14646, hlam]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [h13812, hlam, p14573_0]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [h14565, hlam, p14573_1]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [h14567, hlam, p14573_0]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [h14568, hlam, p14573_0]
                              · have p14573_0 := h14573c.1
                                have p14573_1 := h14573c.2.1
                                have p14573_2 := h14573c.2.2.1
                                have p14573_3 := h14573c.2.2.2
                                linarith only [hlam, p14573_0]
                            · linarith only [h0, h13812, h13813, h14563, h14568, h14572, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h13812, h14481, h14568, h14571, hlam]
                        · linarith only [h13813, h14561, h14570, hlam]
                      · linarith only [h13813, h14560, h14569, hlam]
                    · linarith only [h0, h13813, h14481, h14560, h14562, h14563, h14564, h14568, hc01, hc12, hlam, hphi]
                  · linarith only [h11385, h14561, h14567, hlam]
                · linarith only [h13813, h14560, h14563, h14566, hlam]
              · linarith only [h0, h13813, h14563, h14565, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h13812, h13813, h14563, h14564, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14663 | h14663
            · linarith only [h0, h13812, h14481, h14563, h14663, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14665 | h14665
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14666 | h14666
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14667 | h14667
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14668 | h14668
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14669 | h14669
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14670 | h14670
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14671 | h14671
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14672 | h14672
                            · rcases h1bigk with h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c | h14673c
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [hlam, p14673_0]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [h0, hlam, p14673_0]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [h11385, hlam, p14673_0]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [h12794, hlam, p14673_0]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [h0, h14663, h14665, h14669, h14670, h14672, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14673_1]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [h14663, h14669, hc01, hc23, hlam, hphi, ht12, p14673_1]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [hlam, p14673_0]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [h14563, hlam, p14673_0]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [h14663, hlam, p14673_0]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                rcases p14673_3 (m.d 0 1) (by simp) with h14683 | h14683
                                · linarith only [h0, h14683, hlam]
                                · linarith only [h13812, h14683, hlam]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                rcases p14673_3 (m.d 0 1) (by simp) with h14686 | h14686
                                · linarith only [h14686, hlam, p14673_0]
                                · rcases p14673_3 (m.d 1 2) (by simp) with h14688 | h14688
                                  · linarith only [h14563, h14688, hlam]
                                  · linarith only [h0, h14688, hlam]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [h0, h13812, h14563, h14665, h14670, h14672, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14673_1]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [hlam, p14673_0]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [h12794, h13812, h14563, h14665, h14670, h14672, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14673_1]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                rcases p14673_3 (m.d 0 1) (by simp) with h14694 | h14694
                                · linarith only [h11385, h14694, hlam]
                                · linarith only [h13812, h14694, hlam]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                rcases p14673_3 (m.d 0 1) (by simp) with h14697 | h14697
                                · linarith only [h14697, hlam, p14673_0]
                                · rcases p14673_3 (m.d 1 2) (by simp) with h14699 | h14699
                                  · linarith only [h14663, h14699, hlam]
                                  · linarith only [h0, h14699, hlam]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [h0, h13812, h14665, h14666, h14670, h14672, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p14673_1]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [h14666, hlam, p14673_0]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [hlam, p14673_0]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                rcases p14673_3 (m.d 0 1) (by simp) with h14705 | h14705
                                · linarith only [h12794, h14705, hlam]
                                · linarith only [h13812, h14705, hlam]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [h13812, hlam, p14673_0]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [h14665, hlam, p14673_1]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [h14667, hlam, p14673_0]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [h14668, hlam, p14673_0]
                              · have p14673_0 := h14673c.1
                                have p14673_1 := h14673c.2.1
                                have p14673_2 := h14673c.2.2.1
                                have p14673_3 := h14673c.2.2.2
                                linarith only [hlam, p14673_0]
                            · linarith only [h0, h13812, h14663, h14668, h14669, h14672, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h13812, h14663, h14668, h14671, hlam]
                        · linarith only [h0, h14663, h14669, h14670, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h11385, h14560, h14563, h14669, hlam]
                    · linarith only [h0, h11385, h14560, h14562, h14663, h14668, hc01, hc13, hlam, hphi]
                  · linarith only [h0, h13812, h14561, h14663, h14665, h14666, h14667, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h11385, h13812, h14560, h14665, h14666, hc03, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h13812, h14665, hlam]
        · linarith only [h0, h13812, h14481, h14562, hlam]
      · linarith only [h11385, h13812, h14561, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h14723 | h14723
      · rcases m.htr 0 4 5 (by decide) (by decide) with h14724 | h14724
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14725 | h14725
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14726 | h14726
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14727 | h14727
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14728 | h14728
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14729 | h14729
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14730 | h14730
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14731 | h14731
                      · linarith only [h0, h13813, h14560, h14725, h14731, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h13812, h13813, h14727, h14728, h14731, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h12794, h13812, h14724, h14727, h14730, hc04, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h14560, h14723, h14729, hc13, hc34, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14736 | h14736
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14737 | h14737
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14738 | h14738
                      · linarith only [h14725, h14728, h14738, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14740 | h14740
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14741 | h14741
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14742 | h14742
                            · rcases h1bigk with h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c | h14743c
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [hlam, p14743_0]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [h0, hlam, p14743_0]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [h11385, hlam, p14743_0]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [h12794, hlam, p14743_0]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [h0, h13813, h14725, h14727, h14728, h14740, h14742, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14743_1]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                rcases p14743_3 (m.d 0 1) (by simp) with h14749 | h14749
                                · linarith only [h14749, hlam, p14743_0]
                                · rcases p14743_3 (m.d 1 2) (by simp) with h14751 | h14751
                                  · rcases p14743_3 (m.d 1 3) (by simp) with h14752 | h14752
                                    · linarith only [h14725, h14752, hlam]
                                    · linarith only [h11385, h14752, hlam]
                                  · linarith only [h14751, hlam, p14743_0]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [hlam, p14743_0]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [h0, h13813, h14725, hc01, hc12, hlam, hphi, p14743_1]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [h12794, h13812, h14727, h14740, h14742, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14743_1]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [h0, h13812, h13813, h14725, hlam, p14743_2]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [h13812, h14727, h14728, h14740, h14742, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14743_1]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [h14725, hlam, p14743_1]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [hlam, p14743_0]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [h14728, hlam, p14743_1]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                rcases p14743_3 (m.d 0 1) (by simp) with h14764 | h14764
                                · linarith only [h11385, h14764, hlam]
                                · linarith only [h13812, h14764, hlam]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                rcases p14743_3 (m.d 0 1) (by simp) with h14767 | h14767
                                · linarith only [h14767, hlam, p14743_0]
                                · rcases p14743_3 (m.d 1 2) (by simp) with h14769 | h14769
                                  · rcases p14743_3 (m.d 1 3) (by simp) with h14770 | h14770
                                    · linarith only [h14728, h14770, hlam]
                                    · linarith only [h11385, h14770, hlam]
                                  · linarith only [h0, h14769, hlam]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [h14726, hlam, p14743_1]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [h11385, h13812, h14727, h14740, h14742, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p14743_1]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [hlam, p14743_0]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                rcases p14743_3 (m.d 0 1) (by simp) with h14777 | h14777
                                · linarith only [h12794, h14777, hlam]
                                · linarith only [h13812, h14777, hlam]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [h13812, hlam, p14743_0]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [h14727, hlam, p14743_1]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [h14736, hlam, p14743_0]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [h14737, hlam, p14743_0]
                              · have p14743_0 := h14743c.1
                                have p14743_1 := h14743c.2.1
                                have p14743_2 := h14743c.2.2.1
                                have p14743_3 := h14743c.2.2.2
                                linarith only [hlam, p14743_0]
                            · linarith only [h0, h13813, h14481, h14560, h14724, h14726, h14742, hc01, hc12, hlam, hphi]
                          · linarith only [h12794, h13812, h14481, h14737, h14741, hlam]
                        · linarith only [h0, h13812, h13813, h14560, h14723, h14740, hc04, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h12794, h13812, h14724, h14727, h14737, hc04, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h13812, h13813, h14723, h14725, h14727, h14736, hc03, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h14481, h14726, h14727, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h13812, h13813, h14725, h14726, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14792 | h14792
            · linarith only [h0, h13812, h14481, h14725, h14792, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14794 | h14794
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14795 | h14795
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14796 | h14796
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14797 | h14797
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14798 | h14798
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14799 | h14799
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14800 | h14800
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14801 | h14801
                            · rcases h1bigk with h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c | h14802c
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [hlam, p14802_0]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [h0, hlam, p14802_0]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [h11385, hlam, p14802_0]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [h12794, hlam, p14802_0]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [h0, h14792, h14794, h14798, h14799, h14801, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14802_1]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [h14792, h14798, hc01, hc23, hlam, hphi, ht12, p14802_1]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [hlam, p14802_0]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [h14725, hlam, p14802_0]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [h14792, hlam, p14802_0]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                rcases p14802_3 (m.d 0 1) (by simp) with h14812 | h14812
                                · linarith only [h0, h14812, hlam]
                                · linarith only [h13812, h14812, hlam]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                rcases p14802_3 (m.d 0 1) (by simp) with h14815 | h14815
                                · linarith only [h14815, hlam, p14802_0]
                                · rcases p14802_3 (m.d 1 2) (by simp) with h14817 | h14817
                                  · linarith only [h14725, h14817, hlam]
                                  · linarith only [h0, h14817, hlam]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [h0, h13812, h14725, h14794, h14799, h14801, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14802_1]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [hlam, p14802_0]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [h12794, h13812, h14725, h14794, h14799, h14801, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14802_1]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [h11385, h13812, h14560, h14795, hlam, p14802_2]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                rcases p14802_3 (m.d 0 1) (by simp) with h14824 | h14824
                                · linarith only [h14824, hlam, p14802_0]
                                · rcases p14802_3 (m.d 1 2) (by simp) with h14826 | h14826
                                  · linarith only [h14792, h14826, hlam]
                                  · linarith only [h0, h14826, hlam]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p14802_1]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [h14795, hlam, p14802_0]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [hlam, p14802_0]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                rcases p14802_3 (m.d 0 1) (by simp) with h14832 | h14832
                                · linarith only [h12794, h14832, hlam]
                                · linarith only [h13812, h14832, hlam]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [h13812, hlam, p14802_0]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [h14794, hlam, p14802_1]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [h14796, hlam, p14802_0]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [h14797, hlam, p14802_0]
                              · have p14802_0 := h14802c.1
                                have p14802_1 := h14802c.2.1
                                have p14802_2 := h14802c.2.2.1
                                have p14802_3 := h14802c.2.2.2
                                linarith only [hlam, p14802_0]
                            · linarith only [h14560, h14724, h14801, hlam]
                          · linarith only [h0, h13812, h13813, h14560, h14792, h14797, h14800, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h13813, h14560, h14725, h14795, h14799, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h14725, h14795, h14798, hlam]
                    · linarith only [h12794, h13812, h14724, h14794, h14797, hc04, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h14560, h14723, h14796, hc13, hc34, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14846 | h14846
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14847 | h14847
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14848 | h14848
                      · linarith only [h0, h13812, h14725, h14794, h14795, h14848, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h13812, h14725, h14794, h14848, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h12794, h14724, h14847, hlam]
                  · linarith only [h11385, h14723, h14846, hlam]
              · linarith only [h0, h13812, h14794, hlam]
        · linarith only [h12794, h13812, h14724, hlam]
      · linarith only [h11385, h13812, h14723, hlam]

set_option maxHeartbeats 10168000 in
set_option maxHeartbeats 10168000 in
theorem r1l7_11_23_L_I_H_I_s13_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h13812 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  rcases m.htr 0 2 3 (by decide) (by decide) with h13813 | h13813
  · exact r1l7_11_23_L_I_H_I_s13_x0_x0 m hb1 hb3 hg0 hg11385 hg12794 h13812 h13813
  · exact r1l7_11_23_L_I_H_I_s13_x0_x1 m hb1 hb3 hg0 hg11385 hg12794 h13812 h13813

set_option maxHeartbeats 10168000 in
set_option maxHeartbeats 10168000 in
theorem r1l7_11_23_L_I_H_I_s13_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  exact r1l7_11_23_L_I_H_I_s14 m hb1 hb3 h0 h11385 h12794 h13812

set_option maxHeartbeats 10168000 in
set_option maxHeartbeats 10168000 in
theorem r1l7_11_23_L_I_H_I_s13 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  rcases m.htr 0 1 5 (by decide) (by decide) with h13812 | h13812
  · exact r1l7_11_23_L_I_H_I_s13_x0 m hb1 hb3 hg0 hg11385 hg12794 h13812
  · exact r1l7_11_23_L_I_H_I_s13_x1 m hb1 hb3 hg0 hg11385 hg12794 h13812

end R2N4
