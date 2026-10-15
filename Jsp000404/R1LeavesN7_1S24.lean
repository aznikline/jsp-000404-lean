import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 31062000 in
set_option maxHeartbeats 31062000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h14500 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h14501 | h14501
  · rcases m.htr 0 2 3 (by decide) (by decide) with h14502 | h14502
    · linarith only [h0, h1, h14502, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h14504 | h14504
      · rcases m.htr 0 2 5 (by decide) (by decide) with h14505 | h14505
        · rcases m.htr 0 3 4 (by decide) (by decide) with h14506 | h14506
          · rcases m.htr 0 3 5 (by decide) (by decide) with h14507 | h14507
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14508 | h14508
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14509 | h14509
                · linarith only [h0, h1, h14502, h14504, h14509, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14511 | h14511
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14512 | h14512
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14513 | h14513
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14514 | h14514
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h14515 | h14515
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h14516 | h14516
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14517 | h14517
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h14518 | h14518
                                · linarith only [h0, h1, h14509, h14511, h14518, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h0, h1, h14509, h14511, h14515, h14518, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h1, h14509, h14517, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h14509, h14516, hc12, hc34, hlam, hphi, ht23]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h14523 | h14523
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14524 | h14524
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h14525 | h14525
                                · linarith only [h14511, h14515, h14525, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h14527 | h14527
                                  · linarith only [h14511, h14515, h14523, h14527, hlam]
                                  · rcases h0bigk with h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c | h14529c
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [hlam, p14529_0]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h14504, h14508, h14511, h14515, h14523, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14529_1]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h1, hlam, p14529_0]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h1, h14508, h14509, h14511, h14515, h14523, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14529_1]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h1, h14508, h14509, h14511, h14515, h14523, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14529_1]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h0, hlam, p14529_0]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [hlam, p14529_0]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h14502, hlam, p14529_0]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h14508, h14511, h14515, h14523, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p14529_1]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h0, h1, h14508, h14509, h14511, h14515, h14523, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14529_1]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h0, h1, h14509, hc12, hc23, hlam, hphi, p14529_1]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h1, h14504, h14508, h14509, h14511, h14515, h14523, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14529_1]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [hlam, p14529_0]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h1, h14508, h14509, h14511, h14515, h14523, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14529_1]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      rcases p14529_3 (m.d 0 1) (by simp) with h14544 | h14544
                                      · linarith only [h1, h14544, hlam]
                                      · linarith only [h14501, h14544, hlam]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h14500, hlam, p14529_0]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h14504, hlam, p14529_0]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h14506, hlam, p14529_0]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [hlam, p14529_0]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h0, h1, h14504, h14508, h14509, h14511, h14515, h14523, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14529_1]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h14501, hlam, p14529_0]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h14505, hlam, p14529_1]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h14507, hlam, p14529_0]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [h14508, hlam, p14529_1]
                                    · have p14529_0 := h14529c.1
                                      have p14529_1 := h14529c.2.1
                                      have p14529_2 := h14529c.2.2.1
                                      have p14529_3 := h14529c.2.2.2
                                      linarith only [hlam, p14529_0]
                              · linarith only [h0, h1, h14509, h14524, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h14504, h14508, h14509, h14511, h14515, h14523, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h14514, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h14513, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h1, h14505, h14511, h14512, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h1, h14504, h14509, h14511, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14563 | h14563
                · linarith only [h0, h1, h14502, h14563, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14565 | h14565
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14566 | h14566
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14567 | h14567
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14568 | h14568
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h14569 | h14569
                          · linarith only [h14500, h14508, h14569, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h14571 | h14571
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14572 | h14572
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h14573 | h14573
                                · linarith only [h0, h1, h14508, h14563, h14565, h14573, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h14575 | h14575
                                  · linarith only [h14500, h14508, h14565, h14571, h14575, hlam]
                                  · rcases h0bigk with h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c | h14577c
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      linarith only [hlam, p14577_0]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      linarith only [h1, h14563, hc02, hc23, hlam, hphi, p14577_1]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      linarith only [h1, hlam, p14577_0]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      rcases p14577_3 (m.d 0 1) (by simp) with h14581 | h14581
                                      · rcases p14577_3 (m.d 0 2) (by simp) with h14582 | h14582
                                        · linarith only [h0, h14582, hlam]
                                        · linarith only [h14504, h14582, hlam]
                                      · linarith only [h14500, h14581, hlam]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      rcases p14577_3 (m.d 0 1) (by simp) with h14586 | h14586
                                      · rcases p14577_3 (m.d 0 2) (by simp) with h14587 | h14587
                                        · linarith only [h0, h14587, hlam]
                                        · linarith only [h14505, h14587, hlam]
                                      · linarith only [h14501, h14586, hlam]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      linarith only [h0, hlam, p14577_0]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      linarith only [hlam, p14577_0]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      linarith only [h14502, hlam, p14577_0]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      rcases p14577_3 (m.d 0 1) (by simp) with h14594 | h14594
                                      · rcases p14577_3 (m.d 0 2) (by simp) with h14595 | h14595
                                        · rcases p14577_3 (m.d 0 3) (by simp) with h14596 | h14596
                                          · rcases p14577_3 (m.d 0 4) (by simp) with h14597 | h14597
                                            · linarith only [h14504, h14597, hlam]
                                            · rcases p14577_3 (m.d 0 5) (by simp) with h14599 | h14599
                                              · linarith only [h14505, h14599, hlam]
                                              · linarith only [h14508, h14599, hlam]
                                          · linarith only [h14506, h14596, hlam]
                                        · linarith only [h14504, h14595, hlam]
                                      · linarith only [h14500, h14594, hlam]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      rcases p14577_3 (m.d 0 1) (by simp) with h14605 | h14605
                                      · rcases p14577_3 (m.d 0 2) (by simp) with h14606 | h14606
                                        · rcases p14577_3 (m.d 0 3) (by simp) with h14607 | h14607
                                          · rcases p14577_3 (m.d 0 4) (by simp) with h14608 | h14608
                                            · linarith only [h14504, h14608, hlam]
                                            · rcases p14577_3 (m.d 0 5) (by simp) with h14610 | h14610
                                              · linarith only [h14505, h14610, hlam]
                                              · rcases h2bigk with h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c | h14612c
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [hlam, p14612_0]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [h0, h1, h14563, h14566, h14571, h14573, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14612_1]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [h14502, hlam, p14612_0]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  rcases p14612_3 (m.d 0 2) (by simp) with h14616 | h14616
                                                  · rcases p14612_3 (m.d 1 2) (by simp) with h14617 | h14617
                                                    · linarith only [h0, h14617, hlam]
                                                    · linarith only [h14565, h14617, hlam]
                                                  · linarith only [h14616, hlam, p14612_0]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  rcases p14612_3 (m.d 0 2) (by simp) with h14621 | h14621
                                                  · rcases p14612_3 (m.d 1 2) (by simp) with h14622 | h14622
                                                    · linarith only [h0, h14622, hlam]
                                                    · linarith only [h14566, h14622, hlam]
                                                  · linarith only [h14621, hlam, p14612_0]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [h0, hlam, p14612_0]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [hlam, p14612_0]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [h14563, hlam, p14612_0]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [h0, h1, h14563, h14571, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14612_1]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [h0, h1, h14563, h14571, h14573, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14612_1]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p14577_1, p14612_1]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  rcases p14612_3 (m.d 0 2) (by simp) with h14632 | h14632
                                                  · linarith only [h14502, h14632, hlam]
                                                  · linarith only [h0, h14632, hlam]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [hlam, p14612_0]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [h0, h1, h14500, h14508, h14563, h14565, hlam, p14577_1, p14612_2]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [h0, h1, h14501, h14563, h14566, hlam, p14577_1, p14612_2]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [h14504, hlam, p14612_0]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [h14565, hlam, p14612_0]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [h14571, hlam, p14612_1]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [hlam, p14612_0]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [h14573, hlam, p14612_1]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [h14505, hlam, p14612_0]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [h14566, hlam, p14612_0]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [h14572, hlam, p14612_1]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [h0, h14501, h14566, h14571, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14577_1, p14612_1]
                                                · have p14612_0 := h14612c.1
                                                  have p14612_1 := h14612c.2.1
                                                  have p14612_2 := h14612c.2.2.1
                                                  have p14612_3 := h14612c.2.2.2
                                                  linarith only [hlam, p14612_0]
                                          · linarith only [h14507, h14607, hlam]
                                        · linarith only [h14505, h14606, hlam]
                                      · linarith only [h14501, h14605, hlam]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      linarith only [h0, h1, h14563, hc12, hc23, hlam, hphi, p14577_1]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      rcases p14577_3 (m.d 0 1) (by simp) with h14652 | h14652
                                      · linarith only [h1, h14652, hlam]
                                      · linarith only [h0, h14652, hlam]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      linarith only [hlam, p14577_0]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      rcases p14577_3 (m.d 0 1) (by simp) with h14656 | h14656
                                      · linarith only [h1, h14656, hlam]
                                      · linarith only [h14500, h14656, hlam]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      rcases p14577_3 (m.d 0 1) (by simp) with h14659 | h14659
                                      · linarith only [h1, h14659, hlam]
                                      · linarith only [h14501, h14659, hlam]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      linarith only [h14500, hlam, p14577_0]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      linarith only [h14504, hlam, p14577_0]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      linarith only [h14506, hlam, p14577_0]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      linarith only [hlam, p14577_0]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      linarith only [h14508, hlam, p14577_0]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      linarith only [h14501, hlam, p14577_0]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      linarith only [h14505, hlam, p14577_1]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      linarith only [h14507, hlam, p14577_0]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      rcases p14577_3 (m.d 0 1) (by simp) with h14670 | h14670
                                      · rcases p14577_3 (m.d 0 2) (by simp) with h14671 | h14671
                                        · rcases p14577_3 (m.d 0 3) (by simp) with h14672 | h14672
                                          · rcases p14577_3 (m.d 0 4) (by simp) with h14673 | h14673
                                            · linarith only [h14508, h14673, hlam]
                                            · rcases p14577_3 (m.d 0 5) (by simp) with h14675 | h14675
                                              · rcases h2bigk with h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [hlam, p14676_0]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [h0, h1, h14563, hc12, hc23, hlam, hphi, p14676_1]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [h14502, hlam, p14676_0]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  rcases p14676_3 (m.d 0 2) (by simp) with h14680 | h14680
                                                  · rcases p14676_3 (m.d 1 2) (by simp) with h14681 | h14681
                                                    · linarith only [h0, h14681, hlam]
                                                    · linarith only [h14565, h14681, hlam]
                                                  · linarith only [h14680, hlam, p14676_0]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  rcases p14676_3 (m.d 0 2) (by simp) with h14685 | h14685
                                                  · rcases p14676_3 (m.d 1 2) (by simp) with h14686 | h14686
                                                    · linarith only [h0, h14686, hlam]
                                                    · linarith only [h14566, h14686, hlam]
                                                  · linarith only [h14685, hlam, p14676_0]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [h0, hlam, p14676_0]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [hlam, p14676_0]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [h14563, hlam, p14676_0]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [h0, h1, h14563, h14571, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14676_1]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [h0, h1, h14563, h14572, h14575, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14676_1]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [h14500, h14505, h14565, h14571, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14577_1, p14676_1]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  rcases p14676_3 (m.d 0 2) (by simp) with h14696 | h14696
                                                  · linarith only [h14502, h14696, hlam]
                                                  · linarith only [h0, h14696, hlam]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [hlam, p14676_0]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [h0, h1, h14500, h14505, h14563, h14565, hlam, p14577_1, p14676_2]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [h0, h1, h14563, h14566, hlam, p14676_2]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [h14504, hlam, p14676_0]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [h14565, hlam, p14676_0]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [h14571, hlam, p14676_1]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [hlam, p14676_0]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [h14573, hlam, p14676_1]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [h14505, hlam, p14676_0]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [h14566, hlam, p14676_0]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [h14572, hlam, p14676_1]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [h0, h14566, h14571, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14676_1]
                                                · have p14676_0 := h14676c.1
                                                  have p14676_1 := h14676c.2.1
                                                  have p14676_2 := h14676c.2.2.1
                                                  have p14676_3 := h14676c.2.2.2
                                                  linarith only [hlam, p14676_0]
                                              · linarith only [h14508, h14675, hlam]
                                          · linarith only [h14506, h14672, hlam]
                                        · linarith only [h14504, h14671, hlam]
                                      · linarith only [h14500, h14670, hlam]
                                    · have p14577_0 := h14577c.1
                                      have p14577_1 := h14577c.2.1
                                      have p14577_2 := h14577c.2.2.1
                                      have p14577_3 := h14577c.2.2.2
                                      linarith only [hlam, p14577_0]
                              · linarith only [h0, h1, h14563, h14572, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h14563, h14565, h14571, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h14565, h14568, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h14565, h14567, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h14505, h14565, h14566, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h1, h14504, h14563, h14565, hc12, hc23, hlam, hphi]
            · linarith only [h1, h14501, h14507, hlam]
          · linarith only [h1, h14500, h14506, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h14725 | h14725
          · rcases m.htr 0 3 5 (by decide) (by decide) with h14726 | h14726
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14727 | h14727
              · linarith only [h14504, h14505, h14727, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14729 | h14729
                · linarith only [h0, h1, h14502, h14504, h14729, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14731 | h14731
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14732 | h14732
                    · linarith only [h0, h1, h14505, h14729, h14732, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14734 | h14734
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14735 | h14735
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h14736 | h14736
                          · linarith only [h1, h14500, h14727, h14729, h14736, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h14738 | h14738
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14739 | h14739
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h14740 | h14740
                                · linarith only [h0, h1, h14727, h14729, h14731, h14740, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h14742 | h14742
                                  · linarith only [h0, h14505, h14731, h14738, h14740, h14742, hlam]
                                  · rcases h0bigk with h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c | h14744c
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [hlam, p14744_0]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [h0, h1, h14729, h14731, h14738, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14744_1]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [h1, hlam, p14744_0]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      rcases p14744_3 (m.d 0 1) (by simp) with h14748 | h14748
                                      · rcases p14744_3 (m.d 0 2) (by simp) with h14749 | h14749
                                        · linarith only [h0, h14749, hlam]
                                        · linarith only [h14504, h14749, hlam]
                                      · linarith only [h14500, h14748, hlam]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [h0, h1, h14505, h14729, h14731, h14738, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14744_1]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [h0, hlam, p14744_0]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [hlam, p14744_0]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [h14502, hlam, p14744_0]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [h14500, h14505, h14731, h14738, h14740, hc34, hc45, hlam, hphi, p14744_1]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [h14505, hlam, p14744_0]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [h0, h1, h14729, h14731, h14738, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14744_1]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      rcases p14744_3 (m.d 0 1) (by simp) with h14760 | h14760
                                      · linarith only [h1, h14760, hlam]
                                      · linarith only [h0, h14760, hlam]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [hlam, p14744_0]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      rcases p14744_3 (m.d 0 1) (by simp) with h14764 | h14764
                                      · linarith only [h1, h14764, hlam]
                                      · linarith only [h14500, h14764, hlam]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      rcases p14744_3 (m.d 0 1) (by simp) with h14767 | h14767
                                      · linarith only [h1, h14767, hlam]
                                      · linarith only [h14501, h14767, hlam]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [h14500, hlam, p14744_0]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [h14504, hlam, p14744_0]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [h14725, hlam, p14744_0]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [hlam, p14744_0]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [h14727, hlam, p14744_0]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [h14501, hlam, p14744_0]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [h0, h1, h14501, h14729, h14731, h14738, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14744_1]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [h14726, hlam, p14744_0]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      rcases p14744_3 (m.d 0 1) (by simp) with h14778 | h14778
                                      · rcases p14744_3 (m.d 0 2) (by simp) with h14779 | h14779
                                        · linarith only [h14505, h14779, hlam]
                                        · linarith only [h14504, h14779, hlam]
                                      · linarith only [h14500, h14778, hlam]
                                    · have p14744_0 := h14744c.1
                                      have p14744_1 := h14744c.2.1
                                      have p14744_2 := h14744c.2.2.1
                                      have p14744_3 := h14744c.2.2.2
                                      linarith only [hlam, p14744_0]
                              · linarith only [h0, h1, h14729, h14731, h14738, h14739, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h1, h14501, h14729, h14731, h14732, h14738, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h1, h14501, h14731, h14732, h14735, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h1, h14501, h14731, h14732, h14734, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1, h14504, h14729, h14731, hc12, hc23, hlam, hphi]
            · linarith only [h1, h14501, h14726, hlam]
          · linarith only [h1, h14501, h14504, h14505, h14725, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h14791 | h14791
        · rcases m.htr 0 3 4 (by decide) (by decide) with h14792 | h14792
          · rcases m.htr 0 3 5 (by decide) (by decide) with h14793 | h14793
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14794 | h14794
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14795 | h14795
                · linarith only [h0, h1, h14502, h14795, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14797 | h14797
                  · linarith only [h0, h14504, h14797, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14799 | h14799
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14800 | h14800
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14801 | h14801
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h14802 | h14802
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h14803 | h14803
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14804 | h14804
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h14805 | h14805
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h14806 | h14806
                                  · rcases h0bigk with h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c | h14807c
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [hlam, p14807_0]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [h1, h14795, hc02, hc23, hlam, hphi, p14807_1]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [h1, hlam, p14807_0]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [h0, h1, h14504, h14795, hc12, hc23, hlam, hphi, p14807_1]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      rcases p14807_3 (m.d 0 1) (by simp) with h14812 | h14812
                                      · rcases p14807_3 (m.d 0 2) (by simp) with h14813 | h14813
                                        · linarith only [h0, h14813, hlam]
                                        · linarith only [h14791, h14813, hlam]
                                      · linarith only [h14501, h14812, hlam]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [h0, hlam, p14807_0]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [hlam, p14807_0]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [h14502, hlam, p14807_0]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [h14504, hlam, p14807_1]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      rcases p14807_3 (m.d 0 1) (by simp) with h14821 | h14821
                                      · rcases p14807_3 (m.d 0 2) (by simp) with h14822 | h14822
                                        · rcases p14807_3 (m.d 0 3) (by simp) with h14823 | h14823
                                          · rcases p14807_3 (m.d 0 4) (by simp) with h14824 | h14824
                                            · rcases p14807_3 (m.d 0 5) (by simp) with h14825 | h14825
                                              · linarith only [h14791, h14825, hlam]
                                              · rcases h2bigk with h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c | h14827c
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [hlam, p14827_0]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [h14504, h14799, h14804, h14806, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14827_1]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [h14502, hlam, p14827_0]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [h14504, hlam, p14827_0]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  rcases p14827_3 (m.d 0 2) (by simp) with h14832 | h14832
                                                  · rcases p14827_3 (m.d 1 2) (by simp) with h14833 | h14833
                                                    · linarith only [h0, h14833, hlam]
                                                    · linarith only [h14799, h14833, hlam]
                                                  · linarith only [h14832, hlam, p14827_0]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [h0, hlam, p14827_0]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [hlam, p14827_0]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [h14795, hlam, p14827_0]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [h14797, hlam, p14827_0]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [h0, h1, h14795, h14804, h14806, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14827_1]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [h14501, h14799, h14804, h14806, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14807_1, p14827_1]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  rcases p14827_3 (m.d 0 2) (by simp) with h14843 | h14843
                                                  · linarith only [h14502, h14843, hlam]
                                                  · linarith only [h0, h14843, hlam]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [hlam, p14827_0]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [h14501, h14504, h14799, h14804, h14806, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14807_1, p14827_1]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [h0, h1, h14501, h14795, h14799, hlam, p14807_1, p14827_2]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p14807_1, p14827_1]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  rcases p14827_3 (m.d 0 2) (by simp) with h14850 | h14850
                                                  · linarith only [h14504, h14850, hlam]
                                                  · linarith only [h0, h14850, hlam]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [h14803, hlam, p14827_1]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [hlam, p14827_0]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [h14501, h14504, h14799, hlam, p14807_1, p14827_2]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [h14791, hlam, p14827_0]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [h14799, hlam, p14827_0]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [h14804, hlam, p14827_1]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [h14805, hlam, p14827_0]
                                                · have p14827_0 := h14827c.1
                                                  have p14827_1 := h14827c.2.1
                                                  have p14827_2 := h14827c.2.2.1
                                                  have p14827_3 := h14827c.2.2.2
                                                  linarith only [hlam, p14827_0]
                                            · linarith only [h14794, h14824, hlam]
                                          · linarith only [h14793, h14823, hlam]
                                        · linarith only [h14791, h14822, hlam]
                                      · linarith only [h14501, h14821, hlam]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [h1, h14500, h14795, h14797, hc12, hc23, hlam, hphi, p14807_1]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      rcases p14807_3 (m.d 0 1) (by simp) with h14866 | h14866
                                      · linarith only [h1, h14866, hlam]
                                      · linarith only [h0, h14866, hlam]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [hlam, p14807_0]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      rcases p14807_3 (m.d 0 1) (by simp) with h14870 | h14870
                                      · linarith only [h1, h14870, hlam]
                                      · linarith only [h14500, h14870, hlam]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      rcases p14807_3 (m.d 0 1) (by simp) with h14873 | h14873
                                      · linarith only [h1, h14873, hlam]
                                      · linarith only [h14501, h14873, hlam]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [h14500, hlam, p14807_0]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [h0, h1, h14500, h14795, h14799, h14804, h14806, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14807_1]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [h14792, hlam, p14807_0]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [hlam, p14807_0]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      rcases p14807_3 (m.d 0 1) (by simp) with h14880 | h14880
                                      · rcases p14807_3 (m.d 0 2) (by simp) with h14881 | h14881
                                        · linarith only [h14504, h14881, hlam]
                                        · linarith only [h14791, h14881, hlam]
                                      · linarith only [h14501, h14880, hlam]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [h14501, hlam, p14807_0]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [h14791, hlam, p14807_1]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [h14793, hlam, p14807_0]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [h14794, hlam, p14807_1]
                                    · have p14807_0 := h14807c.1
                                      have p14807_1 := h14807c.2.1
                                      have p14807_2 := h14807c.2.2.1
                                      have p14807_3 := h14807c.2.2.2
                                      linarith only [hlam, p14807_0]
                                  · linarith only [h1, h14500, h14795, h14802, h14806, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h1, h14501, h14504, h14802, h14805, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · linarith only [h1, h14500, h14795, h14797, h14804, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h1, h14500, h14795, h14797, h14799, h14803, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1, h14500, h14794, h14797, h14799, h14802, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h1, h14500, h14797, h14799, h14801, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1, h14500, h14797, h14799, h14800, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h14504, h14791, h14799, hc12, hc24, hlam, hphi]
              · linarith only [h14504, h14791, h14794, hlam]
            · linarith only [h0, h1, h14791, h14793, hlam]
          · linarith only [h1, h14500, h14792, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h14901 | h14901
          · rcases m.htr 0 3 5 (by decide) (by decide) with h14902 | h14902
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14903 | h14903
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14904 | h14904
                · linarith only [h0, h1, h14502, h14904, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14906 | h14906
                  · linarith only [h0, h14504, h14906, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14908 | h14908
                    · linarith only [h0, h14791, h14908, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14910 | h14910
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14911 | h14911
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h14912 | h14912
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h14913 | h14913
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14914 | h14914
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h14915 | h14915
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h14916 | h14916
                                  · rcases h0bigk with h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c | h14917c
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [hlam, p14917_0]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [h0, h1, h14904, hc12, hc23, hlam, hphi, p14917_1]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [h1, hlam, p14917_0]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [h1, h14500, h14904, h14910, h14916, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14917_1]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [h0, h1, h14791, h14904, hc12, hc23, hlam, hphi, p14917_1]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [h0, hlam, p14917_0]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [hlam, p14917_0]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [h14502, hlam, p14917_0]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [h14504, hlam, p14917_1]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [h14791, hlam, p14917_0]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [h0, h1, h14904, hc12, hc23, hlam, hphi, p14917_1]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      rcases p14917_3 (m.d 0 1) (by simp) with h14929 | h14929
                                      · linarith only [h1, h14929, hlam]
                                      · linarith only [h0, h14929, hlam]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [hlam, p14917_0]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      rcases p14917_3 (m.d 0 1) (by simp) with h14933 | h14933
                                      · linarith only [h1, h14933, hlam]
                                      · linarith only [h14500, h14933, hlam]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      rcases p14917_3 (m.d 0 1) (by simp) with h14936 | h14936
                                      · linarith only [h1, h14936, hlam]
                                      · linarith only [h14501, h14936, hlam]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [h14500, hlam, p14917_0]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [h0, h1, h14500, h14904, hc12, hc23, hlam, hphi, p14917_1]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [h14901, hlam, p14917_0]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [hlam, p14917_0]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [h0, h1, h14500, h14791, h14904, hc12, hc23, hlam, hphi, p14917_1]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [h14501, hlam, p14917_0]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [h0, h1, h14501, h14904, hc12, hc23, hlam, hphi, p14917_1]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [h14902, hlam, p14917_0]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [h14903, hlam, p14917_1]
                                    · have p14917_0 := h14917c.1
                                      have p14917_1 := h14917c.2.1
                                      have p14917_2 := h14917c.2.2.1
                                      have p14917_3 := h14917c.2.2.2
                                      linarith only [hlam, p14917_0]
                                  · linarith only [h1, h14500, h14904, h14912, h14916, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h1, h14500, h14904, h14912, h14915, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h1, h14500, h14904, h14912, h14914, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1, h14500, h14904, h14912, h14913, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1, h14500, h14903, h14904, h14906, h14912, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h14911, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h14910, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14956 | h14956
                · linarith only [h0, h14502, h14956, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14958 | h14958
                  · linarith only [h0, h14504, h14958, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14960 | h14960
                    · linarith only [h0, h14791, h14960, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14962 | h14962
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14963 | h14963
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h14964 | h14964
                          · linarith only [h1, h14500, h14903, h14964, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h14966 | h14966
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14967 | h14967
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h14968 | h14968
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h14969 | h14969
                                  · linarith only [h14500, h14903, h14962, h14969, hlam]
                                  · rcases h0bigk with h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c | h14971c
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [hlam, p14971_0]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [h1, h14956, hc02, hc23, hlam, hphi, p14971_1]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [h1, hlam, p14971_0]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [h0, h1, h14504, h14956, hc12, hc23, hlam, hphi, p14971_1]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [h0, h1, h14791, h14956, hc12, hc23, hlam, hphi, p14971_1]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [h0, hlam, p14971_0]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [hlam, p14971_0]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [h14502, hlam, p14971_0]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [h14504, hlam, p14971_1]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [h14791, hlam, p14971_0]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [h0, h14502, hc12, hc23, hlam, hphi, p14971_1]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      rcases p14971_3 (m.d 0 1) (by simp) with h14983 | h14983
                                      · linarith only [h1, h14983, hlam]
                                      · linarith only [h0, h14983, hlam]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [hlam, p14971_0]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      rcases p14971_3 (m.d 0 1) (by simp) with h14987 | h14987
                                      · linarith only [h1, h14987, hlam]
                                      · linarith only [h14500, h14987, hlam]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      rcases p14971_3 (m.d 0 1) (by simp) with h14990 | h14990
                                      · linarith only [h1, h14990, hlam]
                                      · linarith only [h14501, h14990, hlam]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [h14500, hlam, p14971_0]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [h0, h14903, h14968, hc12, hc24, hlam, hphi, p14971_1]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [h14901, hlam, p14971_0]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [hlam, p14971_0]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [h14903, hlam, p14971_0]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [h14501, hlam, p14971_0]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [h0, h1, h14501, h14956, hc12, hc23, hlam, hphi, p14971_1]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [h14902, hlam, p14971_0]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [h0, h1, h14501, h14504, h14956, hc12, hc23, hlam, hphi, p14971_1]
                                    · have p14971_0 := h14971c.1
                                      have p14971_1 := h14971c.2.1
                                      have p14971_2 := h14971c.2.2.1
                                      have p14971_3 := h14971c.2.2.2
                                      linarith only [hlam, p14971_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h15003 | h15003
                                  · linarith only [h1, h14500, h14956, h14962, h14968, h15003, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · rcases h0bigk with h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c | h15005c
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [hlam, p15005_0]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [h0, h1, h14956, hc12, hc23, hlam, hphi, p15005_1]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [h1, hlam, p15005_0]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [h0, h1, h14504, h14956, hc12, hc23, hlam, hphi, p15005_1]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [h0, h1, h14791, h14956, hc12, hc23, hlam, hphi, p15005_1]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [h0, hlam, p15005_0]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [hlam, p15005_0]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [h14502, hlam, p15005_0]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [h14504, hlam, p15005_1]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [h14791, hlam, p15005_0]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [h0, h1, h14956, hc12, hc23, hlam, hphi, p15005_1]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      rcases p15005_3 (m.d 0 1) (by simp) with h15017 | h15017
                                      · linarith only [h1, h15017, hlam]
                                      · linarith only [h0, h15017, hlam]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [hlam, p15005_0]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      rcases p15005_3 (m.d 0 1) (by simp) with h15021 | h15021
                                      · linarith only [h1, h15021, hlam]
                                      · linarith only [h14500, h15021, hlam]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      rcases p15005_3 (m.d 0 1) (by simp) with h15024 | h15024
                                      · linarith only [h1, h15024, hlam]
                                      · linarith only [h14501, h15024, hlam]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [h14500, hlam, p15005_0]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [h0, h1, h14500, h14956, hc12, hc23, hlam, hphi, p15005_1]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [h14901, hlam, p15005_0]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [hlam, p15005_0]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [h14903, hlam, p15005_0]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [h14501, hlam, p15005_0]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [h0, h1, h14501, h14956, hc12, hc23, hlam, hphi, p15005_1]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [h14902, hlam, p15005_0]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [h1, h14500, h14501, h14956, h14958, hc12, hc23, hlam, hphi, p15005_1]
                                    · have p15005_0 := h15005c.1
                                      have p15005_1 := h15005c.2.1
                                      have p15005_2 := h15005c.2.2.1
                                      have p15005_3 := h15005c.2.2.2
                                      linarith only [hlam, p15005_0]
                              · linarith only [h0, h1, h14956, h14967, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h1, h14501, h14956, h14958, h14964, h14966, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1, h14963, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h14501, h14960, h14962, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h14501, h14902, hlam]
          · linarith only [h1, h14500, h14901, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h15043 | h15043
    · linarith only [h0, h1, h15043, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h15045 | h15045
      · rcases m.htr 0 2 5 (by decide) (by decide) with h15046 | h15046
        · linarith only [h0, h14501, h15046, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h15048 | h15048
          · rcases m.htr 0 3 5 (by decide) (by decide) with h15049 | h15049
            · rcases m.htr 0 4 5 (by decide) (by decide) with h15050 | h15050
              · linarith only [h0, h14501, h15045, h15050, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h15052 | h15052
                · linarith only [h0, h1, h15043, h15052, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h15054 | h15054
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15055 | h15055
                    · linarith only [h0, h14501, h15046, h15055, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h15057 | h15057
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h15058 | h15058
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h15059 | h15059
                          · linarith only [h14500, h14501, h15050, h15052, h15058, h15059, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h14501, h15054, h15059, hc24, hc45, hlam, hphi]
                        · linarith only [h0, h1, h15049, h15054, h15058, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h15054, h15057, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h15043, h15045, h15054, hc12, hc23, hlam, hphi]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h15065 | h15065
              · linarith only [h0, h1, h15045, h15049, h15065, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h15067 | h15067
                · linarith only [h0, h1, h15049, h15067, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h15069 | h15069
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15070 | h15070
                    · linarith only [h0, h1, h15046, h15049, h15070, hc02, hc35, hlam, hphi, ht23]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h15072 | h15072
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h15073 | h15073
                        · linarith only [h0, h1, h15049, h15069, h15073, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h1, h15069, h15073, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h15069, h15072, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h15043, h15045, h15069, hc12, hc23, hlam, hphi]
          · linarith only [h0, h1, h15045, h15048, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h15079 | h15079
        · linarith only [h14500, h14501, h15045, h15079, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h15081 | h15081
          · rcases m.htr 0 3 5 (by decide) (by decide) with h15082 | h15082
            · rcases m.htr 0 4 5 (by decide) (by decide) with h15083 | h15083
              · linarith only [h14500, h14501, h15083, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h15085 | h15085
                · linarith only [h0, h15043, h15085, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h15087 | h15087
                  · linarith only [h0, h15045, h15087, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15089 | h15089
                    · linarith only [h0, h14501, h15079, h15089, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h15091 | h15091
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h15092 | h15092
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h15093 | h15093
                          · linarith only [h14500, h14501, h15083, h15093, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h15095 | h15095
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h15096 | h15096
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h15097 | h15097
                                · linarith only [h14500, h14501, h15087, h15093, h15095, h15097, hc12, hc23, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h15099 | h15099
                                  · linarith only [h14500, h15045, h15091, h15097, h15099, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                  · rcases h0bigk with h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c | h15101c
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [hlam, p15101_0]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [h0, h14501, h15089, h15097, hc12, hc45, hlam, hphi, ht23, ht34, p15101_1]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [h1, hlam, p15101_0]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [h14501, h15089, h15097, hc04, hc45, hlam, hphi, p15101_1]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [h14501, hlam, p15101_1]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [h0, hlam, p15101_0]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [hlam, p15101_0]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [h15043, hlam, p15101_0]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [h15045, hlam, p15101_1]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [h15079, hlam, p15101_0]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [h0, h15043, hc12, hc23, hlam, hphi, p15101_1]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      rcases p15101_3 (m.d 0 1) (by simp) with h15113 | h15113
                                      · linarith only [h1, h15113, hlam]
                                      · linarith only [h0, h15113, hlam]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [hlam, p15101_0]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      rcases p15101_3 (m.d 0 1) (by simp) with h15117 | h15117
                                      · linarith only [h1, h15117, hlam]
                                      · linarith only [h14500, h15117, hlam]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [h1, h14500, h14501, h15085, h15087, hc12, hc23, hlam, hphi, p15101_1]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [h14500, hlam, p15101_0]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [h0, h14500, h14501, h15089, hc12, hc25, hlam, hphi, p15101_1]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [h15081, hlam, p15101_0]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [hlam, p15101_0]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [h15083, hlam, p15101_0]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [h0, h14501, h15089, h15097, hc12, hc45, hlam, hphi, ht23, ht34, p15101_1]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      rcases p15101_3 (m.d 0 1) (by simp) with h15127 | h15127
                                      · linarith only [h14501, h15127, hlam]
                                      · linarith only [h0, h15127, hlam]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [h15082, hlam, p15101_0]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      rcases p15101_3 (m.d 0 1) (by simp) with h15131 | h15131
                                      · linarith only [h14501, h15131, hlam]
                                      · linarith only [h14500, h15131, hlam]
                                    · have p15101_0 := h15101c.1
                                      have p15101_1 := h15101c.2.1
                                      have p15101_2 := h15101c.2.2.1
                                      have p15101_3 := h15101c.2.2.2
                                      linarith only [hlam, p15101_0]
                              · linarith only [h1, h15082, h15085, h15096, hlam]
                            · linarith only [h1, h14500, h15085, h15091, h15095, hlam]
                        · linarith only [h1, h15082, h15092, hlam]
                      · linarith only [h1, h14500, h15087, h15091, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h15139 | h15139
              · linarith only [h14500, h14501, h15139, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h15141 | h15141
                · linarith only [h0, h1, h15082, h15141, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h15143 | h15143
                  · linarith only [h0, h15045, h15143, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15145 | h15145
                    · linarith only [h1, h14500, h15079, h15082, h15143, h15145, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h15147 | h15147
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h15148 | h15148
                        · linarith only [h1, h14500, h15082, h15141, h15143, h15148, hc12, hc23, hlam, hphi]
                        · linarith only [h1, h14500, h15143, h15148, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h14500, h15143, h15147, hc12, hc34, hlam, hphi, ht23]
          · linarith only [h1, h14500, h15081, hlam]

end R2N4
