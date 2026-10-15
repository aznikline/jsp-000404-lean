import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S44

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h26247 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h26249 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h26251 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h26252 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  rcases m.htr 1 4 5 (by decide) (by decide) with h27576 | h27576
  · linarith only [h2, h23339, h27576, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h27578 | h27578
    · rcases m.htr 2 3 5 (by decide) (by decide) with h27579 | h27579
      · rcases m.htr 2 4 5 (by decide) (by decide) with h27580 | h27580
        · rcases m.htr 3 4 5 (by decide) (by decide) with h27581 | h27581
          · linarith only [h23338, h23339, h26251, h26252, h27581, hlam]
          · rcases h1bigk with h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c | h27583c
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [hlam, p27583_0]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              rcases p27583_3 (m.d 0 1) (by simp) with h27585 | h27585
              · rcases p27583_3 (m.d 1 2) (by simp) with h27586 | h27586
                · linarith only [h27586, hlam, p27583_0]
                · rcases p27583_3 (m.d 1 3) (by simp) with h27588 | h27588
                  · linarith only [h1, h27588, hlam]
                  · linarith only [h26245, h27588, hlam]
              · linarith only [h27585, hlam, p27583_0]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              rcases p27583_3 (m.d 0 1) (by simp) with h27592 | h27592
              · rcases p27583_3 (m.d 1 2) (by simp) with h27593 | h27593
                · linarith only [h0, h27593, hlam]
                · rcases p27583_3 (m.d 1 3) (by simp) with h27595 | h27595
                  · linarith only [h27595, hlam, p27583_0]
                  · rcases p27583_3 (m.d 1 4) (by simp) with h27597 | h27597
                    · linarith only [h2, h27597, hlam]
                    · rcases p27583_3 (m.d 1 5) (by simp) with h27599 | h27599
                      · linarith only [h27599, h3, hlam]
                      · linarith only [h26252, h27599, hlam]
              · linarith only [h27592, hlam, p27583_0]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              rcases p27583_3 (m.d 0 1) (by simp) with h27603 | h27603
              · rcases p27583_3 (m.d 1 2) (by simp) with h27604 | h27604
                · linarith only [h0, h27604, hlam]
                · rcases p27583_3 (m.d 1 3) (by simp) with h27606 | h27606
                  · linarith only [h1, h27606, hlam]
                  · linarith only [h26251, h27606, hlam]
              · linarith only [h27603, hlam, p27583_0]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              rcases p27583_3 (m.d 0 1) (by simp) with h27610 | h27610
              · rcases p27583_3 (m.d 1 2) (by simp) with h27611 | h27611
                · linarith only [h0, h27611, hlam]
                · rcases p27583_3 (m.d 1 3) (by simp) with h27613 | h27613
                  · linarith only [h1, h27613, hlam]
                  · rcases p27583_3 (m.d 1 4) (by simp) with h27615 | h27615
                    · linarith only [h2, h27615, hlam]
                    · rcases p27583_3 (m.d 1 5) (by simp) with h27617 | h27617
                      · linarith only [h27617, hlam, p27583_0]
                      · rcases h1emax with h27619 | h27619 | h27619 | h27619 | h27619
                        · linarith only [h27619, hc15, hlam, hphi, ht01, ht0b, ht5b, p27583_1]
                        · rcases h2bigk with h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c | h27621c
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [hlam, p27621_0]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p27621_1]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [h4, hlam, p27621_0]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [h19744, hlam, p27621_0]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [h22010, hlam, p27621_0]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [h0, hlam, p27621_1]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [hlam, p27621_0]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [h26245, hlam, p27621_0]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [h26247, hlam, p27621_0]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [h26249, hlam, p27621_0]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            rcases p27621_3 (m.d 0 2) (by simp) with h27632 | h27632
                            · linarith only [h27632, hlam, p27621_0]
                            · rcases p27621_3 (m.d 1 2) (by simp) with h27634 | h27634
                              · linarith only [h26245, h27634, hlam]
                              · rcases p27621_3 (m.d 2 3) (by simp) with h27636 | h27636
                                · rcases p27621_3 (m.d 2 4) (by simp) with h27637 | h27637
                                  · linarith only [h27578, h27637, hlam]
                                  · linarith only [h19744, h27637, hlam]
                                · linarith only [h27636, hlam, p27621_0]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            rcases p27621_3 (m.d 0 2) (by simp) with h27641 | h27641
                            · linarith only [h27641, h4, hlam]
                            · linarith only [h0, h27641, hlam]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [hlam, p27621_0]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [h23338, h23339, h26251, h26252, h27580, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p27621_1]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [h22010, hc02, hc23, hlam, hphi, p27621_1]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            rcases p27621_3 (m.d 0 2) (by simp) with h27647 | h27647
                            · linarith only [h27647, hlam, p27621_0]
                            · rcases p27621_3 (m.d 1 2) (by simp) with h27649 | h27649
                              · linarith only [h26247, h27649, hlam]
                              · rcases p27621_3 (m.d 2 3) (by simp) with h27651 | h27651
                                · rcases p27621_3 (m.d 2 4) (by simp) with h27652 | h27652
                                  · rcases p27621_3 (m.d 2 5) (by simp) with h27653 | h27653
                                    · linarith only [h27580, h27653, hlam]
                                    · linarith only [h22010, h27653, hlam]
                                  · linarith only [h27652, hlam, p27621_0]
                                · linarith only [h27651, h4, hlam]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            rcases p27621_3 (m.d 0 2) (by simp) with h27658 | h27658
                            · linarith only [h19744, h27658, hlam]
                            · linarith only [h0, h27658, hlam]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [h27578, hlam, p27621_0]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [hlam, p27621_0]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [h23338, h23339, h26251, h26252, h27580, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p27621_1]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            rcases p27621_3 (m.d 0 2) (by simp) with h27664 | h27664
                            · linarith only [h27664, hlam, p27621_0]
                            · rcases p27621_3 (m.d 1 2) (by simp) with h27666 | h27666
                              · linarith only [h26249, h27666, hlam]
                              · rcases p27621_3 (m.d 2 3) (by simp) with h27668 | h27668
                                · rcases p27621_3 (m.d 2 4) (by simp) with h27669 | h27669
                                  · rcases p27621_3 (m.d 2 5) (by simp) with h27670 | h27670
                                    · rcases h4bigk with h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c | h27671c
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [hlam, p27671_0]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [h23339, h26247, hc12, hc45, hlam, hphi, ht23, ht34, p27671_1]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [h19744, hlam, p27671_1]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [h23339, hc34, hc45, hlam, hphi, p27671_1]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [h23339, hlam, p27671_0]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [h2, hlam, p27671_0]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [hlam, p27671_0]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [h26247, hlam, p27671_1]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [h2, h23339, hc34, hc45, hlam, hphi, p27671_1]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [h27576, hlam, p27671_0]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        rcases p27671_3 (m.d 0 4) (by simp) with h27682 | h27682
                                        · linarith only [h19744, h27682, hlam]
                                        · rcases p27671_3 (m.d 1 4) (by simp) with h27684 | h27684
                                          · linarith only [h26247, h27684, hlam]
                                          · rcases p27671_3 (m.d 2 4) (by simp) with h27686 | h27686
                                            · rcases p27671_3 (m.d 3 4) (by simp) with h27687 | h27687
                                              · linarith only [h27578, h27687, hlam]
                                              · rcases p27671_3 (m.d 4 5) (by simp) with h27689 | h27689
                                                · linarith only [h27580, h27689, hlam]
                                                · linarith only [h23339, h27689, hlam]
                                            · linarith only [h19744, h27686, hlam]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        rcases p27671_3 (m.d 0 4) (by simp) with h27693 | h27693
                                        · linarith only [h19744, h27693, hlam]
                                        · linarith only [h2, h27693, hlam]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [hlam, p27671_0]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [h23338, h23339, h26251, h26252, h27580, hlam, p27671_2]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [h23338, h23339, h26251, h26252, h27578, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p27671_1]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [h23337, hlam, p27671_0]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [h26251, hlam, p27671_0]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [h27578, hlam, p27671_0]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [hlam, p27671_0]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [h27581, hlam, p27671_0]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [h0, h19744, h27578, h27580, hc12, hc23, hlam, hphi, p27671_1]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [h26247, h27578, h27580, hc12, hc23, hlam, hphi, p27671_1]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [h27580, hlam, p27671_0]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        rcases p27671_3 (m.d 0 4) (by simp) with h27707 | h27707
                                        · linarith only [h23339, h27707, hlam]
                                        · linarith only [h23337, h27707, hlam]
                                      · have p27671_0 := h27671c.1
                                        have p27671_1 := h27671c.2.1
                                        have p27671_2 := h27671c.2.2.1
                                        have p27671_3 := h27671c.2.2.2
                                        linarith only [hlam, p27671_0]
                                    · linarith only [h27670, hlam, p27621_0]
                                  · linarith only [h19744, h27669, hlam]
                                · linarith only [h27668, h4, hlam]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            rcases p27621_3 (m.d 0 2) (by simp) with h27714 | h27714
                            · linarith only [h22010, h27714, hlam]
                            · linarith only [h0, h27714, hlam]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [h27579, hlam, p27621_0]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [h27580, hlam, p27621_1]
                          · have p27621_0 := h27621c.1
                            have p27621_1 := h27621c.2.1
                            have p27621_2 := h27621c.2.2.1
                            have p27621_3 := h27621c.2.2.2
                            linarith only [hlam, p27621_0]
                        · rcases h2bigk with h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c | h27720c
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [hlam, p27720_0]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p27720_1]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [h4, hlam, p27720_0]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [h19744, hlam, p27720_0]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [h22010, hlam, p27720_0]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [h0, hlam, p27720_1]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [hlam, p27720_0]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [h26245, hlam, p27720_0]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [h26247, hlam, p27720_0]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [h26249, hlam, p27720_0]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            rcases p27720_3 (m.d 0 2) (by simp) with h27731 | h27731
                            · linarith only [h27731, hlam, p27720_0]
                            · rcases p27720_3 (m.d 1 2) (by simp) with h27733 | h27733
                              · linarith only [h26245, h27733, hlam]
                              · rcases p27720_3 (m.d 2 3) (by simp) with h27735 | h27735
                                · rcases p27720_3 (m.d 2 4) (by simp) with h27736 | h27736
                                  · linarith only [h27578, h27736, hlam]
                                  · linarith only [h19744, h27736, hlam]
                                · linarith only [h27735, hlam, p27720_0]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            rcases p27720_3 (m.d 0 2) (by simp) with h27740 | h27740
                            · linarith only [h27740, h4, hlam]
                            · linarith only [h0, h27740, hlam]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [hlam, p27720_0]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [h19744, h23339, h27580, hc02, hc23, hlam, hphi, p27720_1]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [h0, h22010, hc12, hc23, hlam, hphi, p27720_1]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            rcases p27720_3 (m.d 0 2) (by simp) with h27746 | h27746
                            · linarith only [h27746, hlam, p27720_0]
                            · rcases p27720_3 (m.d 1 2) (by simp) with h27748 | h27748
                              · linarith only [h26247, h27748, hlam]
                              · rcases p27720_3 (m.d 2 3) (by simp) with h27750 | h27750
                                · rcases p27720_3 (m.d 2 4) (by simp) with h27751 | h27751
                                  · rcases p27720_3 (m.d 2 5) (by simp) with h27752 | h27752
                                    · linarith only [h27580, h27752, hlam]
                                    · linarith only [h22010, h27752, hlam]
                                  · linarith only [h27751, hlam, p27720_0]
                                · linarith only [h27750, h4, hlam]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            rcases p27720_3 (m.d 0 2) (by simp) with h27757 | h27757
                            · linarith only [h19744, h27757, hlam]
                            · linarith only [h0, h27757, hlam]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [h27578, hlam, p27720_0]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [hlam, p27720_0]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [h23338, h23339, h26251, h26252, h27580, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p27720_1]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            rcases p27720_3 (m.d 0 2) (by simp) with h27763 | h27763
                            · linarith only [h27763, hlam, p27720_0]
                            · rcases p27720_3 (m.d 1 2) (by simp) with h27765 | h27765
                              · linarith only [h26249, h27765, hlam]
                              · rcases p27720_3 (m.d 2 3) (by simp) with h27767 | h27767
                                · rcases p27720_3 (m.d 2 4) (by simp) with h27768 | h27768
                                  · rcases p27720_3 (m.d 2 5) (by simp) with h27769 | h27769
                                    · rcases h4bigk with h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c | h27770c
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [hlam, p27770_0]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [h23339, h26247, hc12, hc45, hlam, hphi, ht23, ht34, p27770_1]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [h19744, hlam, p27770_1]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [h23339, hc34, hc45, hlam, hphi, p27770_1]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [h23339, hlam, p27770_0]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [h2, hlam, p27770_0]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [hlam, p27770_0]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [h26247, hlam, p27770_1]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [h2, h23339, hc34, hc45, hlam, hphi, p27770_1]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [h27576, hlam, p27770_0]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        rcases p27770_3 (m.d 0 4) (by simp) with h27781 | h27781
                                        · linarith only [h19744, h27781, hlam]
                                        · rcases p27770_3 (m.d 1 4) (by simp) with h27783 | h27783
                                          · linarith only [h26247, h27783, hlam]
                                          · rcases p27770_3 (m.d 2 4) (by simp) with h27785 | h27785
                                            · rcases p27770_3 (m.d 3 4) (by simp) with h27786 | h27786
                                              · linarith only [h27578, h27786, hlam]
                                              · rcases p27770_3 (m.d 4 5) (by simp) with h27788 | h27788
                                                · linarith only [h27580, h27788, hlam]
                                                · linarith only [h23339, h27788, hlam]
                                            · linarith only [h19744, h27785, hlam]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        rcases p27770_3 (m.d 0 4) (by simp) with h27792 | h27792
                                        · linarith only [h19744, h27792, hlam]
                                        · linarith only [h2, h27792, hlam]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [hlam, p27770_0]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [h23338, h23339, h26251, h26252, h27580, hlam, p27770_2]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [h23338, h23339, h26251, h26252, h27578, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p27770_1]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [h23337, hlam, p27770_0]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [h26251, hlam, p27770_0]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [h27578, hlam, p27770_0]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [hlam, p27770_0]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [h27581, hlam, p27770_0]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [h0, h19744, h27578, h27580, hc12, hc23, hlam, hphi, p27770_1]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [h26247, h27578, h27580, hc12, hc23, hlam, hphi, p27770_1]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [h27580, hlam, p27770_0]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        rcases p27770_3 (m.d 0 4) (by simp) with h27806 | h27806
                                        · linarith only [h23339, h27806, hlam]
                                        · linarith only [h23337, h27806, hlam]
                                      · have p27770_0 := h27770c.1
                                        have p27770_1 := h27770c.2.1
                                        have p27770_2 := h27770c.2.2.1
                                        have p27770_3 := h27770c.2.2.2
                                        linarith only [hlam, p27770_0]
                                    · linarith only [h27769, hlam, p27720_0]
                                  · linarith only [h19744, h27768, hlam]
                                · linarith only [h27767, h4, hlam]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            rcases p27720_3 (m.d 0 2) (by simp) with h27813 | h27813
                            · linarith only [h22010, h27813, hlam]
                            · linarith only [h0, h27813, hlam]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [h27579, hlam, p27720_0]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [h27580, hlam, p27720_1]
                          · have p27720_0 := h27720c.1
                            have p27720_1 := h27720c.2.1
                            have p27720_2 := h27720c.2.2.1
                            have p27720_3 := h27720c.2.2.2
                            linarith only [hlam, p27720_0]
                        · rcases h2bigk with h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c | h27819c
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [hlam, p27819_0]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p27819_1]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [h4, hlam, p27819_0]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [h19744, hlam, p27819_0]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [h22010, hlam, p27819_0]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [h0, hlam, p27819_1]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [hlam, p27819_0]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [h26245, hlam, p27819_0]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [h26247, hlam, p27819_0]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [h26249, hlam, p27819_0]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            rcases p27819_3 (m.d 0 2) (by simp) with h27830 | h27830
                            · linarith only [h27830, hlam, p27819_0]
                            · rcases p27819_3 (m.d 1 2) (by simp) with h27832 | h27832
                              · linarith only [h26245, h27832, hlam]
                              · rcases p27819_3 (m.d 2 3) (by simp) with h27834 | h27834
                                · rcases p27819_3 (m.d 2 4) (by simp) with h27835 | h27835
                                  · linarith only [h27578, h27835, hlam]
                                  · linarith only [h19744, h27835, hlam]
                                · linarith only [h27834, hlam, p27819_0]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            rcases p27819_3 (m.d 0 2) (by simp) with h27839 | h27839
                            · linarith only [h27839, h4, hlam]
                            · linarith only [h0, h27839, hlam]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [hlam, p27819_0]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [h19744, h23339, h27580, hc02, hc23, hlam, hphi, p27819_1]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [h0, h22010, hc12, hc23, hlam, hphi, p27819_1]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            rcases p27819_3 (m.d 0 2) (by simp) with h27845 | h27845
                            · linarith only [h27845, hlam, p27819_0]
                            · rcases p27819_3 (m.d 1 2) (by simp) with h27847 | h27847
                              · linarith only [h26247, h27847, hlam]
                              · rcases p27819_3 (m.d 2 3) (by simp) with h27849 | h27849
                                · rcases p27819_3 (m.d 2 4) (by simp) with h27850 | h27850
                                  · rcases p27819_3 (m.d 2 5) (by simp) with h27851 | h27851
                                    · linarith only [h27580, h27851, hlam]
                                    · linarith only [h22010, h27851, hlam]
                                  · linarith only [h27850, hlam, p27819_0]
                                · linarith only [h27849, h4, hlam]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            rcases p27819_3 (m.d 0 2) (by simp) with h27856 | h27856
                            · linarith only [h19744, h27856, hlam]
                            · linarith only [h0, h27856, hlam]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [h27578, hlam, p27819_0]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [hlam, p27819_0]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [h23338, h23339, h26251, h26252, h27580, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p27819_1]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            rcases p27819_3 (m.d 0 2) (by simp) with h27862 | h27862
                            · linarith only [h27862, hlam, p27819_0]
                            · rcases p27819_3 (m.d 1 2) (by simp) with h27864 | h27864
                              · linarith only [h26249, h27864, hlam]
                              · rcases p27819_3 (m.d 2 3) (by simp) with h27866 | h27866
                                · rcases p27819_3 (m.d 2 4) (by simp) with h27867 | h27867
                                  · rcases p27819_3 (m.d 2 5) (by simp) with h27868 | h27868
                                    · rcases h4bigk with h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c | h27869c
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [hlam, p27869_0]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [h23339, h26247, hc12, hc45, hlam, hphi, ht23, ht34, p27869_1]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [h19744, hlam, p27869_1]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [h23339, hc34, hc45, hlam, hphi, p27869_1]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [h23339, hlam, p27869_0]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [h2, hlam, p27869_0]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [hlam, p27869_0]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [h26247, hlam, p27869_1]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [h2, h23339, hc34, hc45, hlam, hphi, p27869_1]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [h27576, hlam, p27869_0]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        rcases p27869_3 (m.d 0 4) (by simp) with h27880 | h27880
                                        · linarith only [h19744, h27880, hlam]
                                        · rcases p27869_3 (m.d 1 4) (by simp) with h27882 | h27882
                                          · linarith only [h26247, h27882, hlam]
                                          · rcases p27869_3 (m.d 2 4) (by simp) with h27884 | h27884
                                            · rcases p27869_3 (m.d 3 4) (by simp) with h27885 | h27885
                                              · linarith only [h27578, h27885, hlam]
                                              · rcases p27869_3 (m.d 4 5) (by simp) with h27887 | h27887
                                                · linarith only [h27580, h27887, hlam]
                                                · linarith only [h23339, h27887, hlam]
                                            · linarith only [h19744, h27884, hlam]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        rcases p27869_3 (m.d 0 4) (by simp) with h27891 | h27891
                                        · linarith only [h19744, h27891, hlam]
                                        · linarith only [h2, h27891, hlam]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [hlam, p27869_0]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [h23338, h23339, h26251, h26252, h27580, hlam, p27869_2]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [h23338, h23339, h26251, h26252, h27578, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p27869_1]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [h23337, hlam, p27869_0]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [h26251, hlam, p27869_0]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [h27578, hlam, p27869_0]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [hlam, p27869_0]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [h27581, hlam, p27869_0]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [h0, h19744, h27578, h27580, hc12, hc23, hlam, hphi, p27869_1]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [h26247, h27578, h27580, hc12, hc23, hlam, hphi, p27869_1]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [h27580, hlam, p27869_0]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        rcases p27869_3 (m.d 0 4) (by simp) with h27905 | h27905
                                        · linarith only [h23339, h27905, hlam]
                                        · linarith only [h23337, h27905, hlam]
                                      · have p27869_0 := h27869c.1
                                        have p27869_1 := h27869c.2.1
                                        have p27869_2 := h27869c.2.2.1
                                        have p27869_3 := h27869c.2.2.2
                                        linarith only [hlam, p27869_0]
                                    · linarith only [h27868, hlam, p27819_0]
                                  · linarith only [h19744, h27867, hlam]
                                · linarith only [h27866, h4, hlam]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            rcases p27819_3 (m.d 0 2) (by simp) with h27912 | h27912
                            · linarith only [h22010, h27912, hlam]
                            · linarith only [h0, h27912, hlam]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [h27579, hlam, p27819_0]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [h27580, hlam, p27819_1]
                          · have p27819_0 := h27819c.1
                            have p27819_1 := h27819c.2.1
                            have p27819_2 := h27819c.2.2.1
                            have p27819_3 := h27819c.2.2.2
                            linarith only [hlam, p27819_0]
                        · rcases h2bigk with h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c | h27918c
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [hlam, p27918_0]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p27918_1]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [h4, hlam, p27918_0]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [h19744, hlam, p27918_0]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [h22010, hlam, p27918_0]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [h0, hlam, p27918_1]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [hlam, p27918_0]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [h26245, hlam, p27918_0]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [h26247, hlam, p27918_0]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [h26249, hlam, p27918_0]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            rcases p27918_3 (m.d 0 2) (by simp) with h27929 | h27929
                            · linarith only [h27929, hlam, p27918_0]
                            · rcases p27918_3 (m.d 1 2) (by simp) with h27931 | h27931
                              · linarith only [h26245, h27931, hlam]
                              · rcases p27918_3 (m.d 2 3) (by simp) with h27933 | h27933
                                · rcases p27918_3 (m.d 2 4) (by simp) with h27934 | h27934
                                  · linarith only [h27578, h27934, hlam]
                                  · linarith only [h19744, h27934, hlam]
                                · linarith only [h27933, hlam, p27918_0]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            rcases p27918_3 (m.d 0 2) (by simp) with h27938 | h27938
                            · linarith only [h27938, h4, hlam]
                            · linarith only [h0, h27938, hlam]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [hlam, p27918_0]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [h19744, h23339, h27580, hc02, hc23, hlam, hphi, p27918_1]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [h0, h22010, hc12, hc23, hlam, hphi, p27918_1]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            rcases p27918_3 (m.d 0 2) (by simp) with h27944 | h27944
                            · linarith only [h27944, hlam, p27918_0]
                            · rcases p27918_3 (m.d 1 2) (by simp) with h27946 | h27946
                              · linarith only [h26247, h27946, hlam]
                              · rcases p27918_3 (m.d 2 3) (by simp) with h27948 | h27948
                                · rcases p27918_3 (m.d 2 4) (by simp) with h27949 | h27949
                                  · rcases p27918_3 (m.d 2 5) (by simp) with h27950 | h27950
                                    · linarith only [h27580, h27950, hlam]
                                    · linarith only [h22010, h27950, hlam]
                                  · linarith only [h27949, hlam, p27918_0]
                                · linarith only [h27948, h4, hlam]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            rcases p27918_3 (m.d 0 2) (by simp) with h27955 | h27955
                            · linarith only [h19744, h27955, hlam]
                            · linarith only [h0, h27955, hlam]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [h27578, hlam, p27918_0]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [hlam, p27918_0]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [h23338, h23339, h26251, h26252, h27580, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p27918_1]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            rcases p27918_3 (m.d 0 2) (by simp) with h27961 | h27961
                            · linarith only [h27961, hlam, p27918_0]
                            · rcases p27918_3 (m.d 1 2) (by simp) with h27963 | h27963
                              · linarith only [h26249, h27963, hlam]
                              · rcases p27918_3 (m.d 2 3) (by simp) with h27965 | h27965
                                · rcases p27918_3 (m.d 2 4) (by simp) with h27966 | h27966
                                  · rcases p27918_3 (m.d 2 5) (by simp) with h27967 | h27967
                                    · rcases h4bigk with h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c | h27968c
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [hlam, p27968_0]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [h23339, h26247, hc12, hc45, hlam, hphi, ht23, ht34, p27968_1]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [h19744, hlam, p27968_1]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [h23339, hc34, hc45, hlam, hphi, p27968_1]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [h23339, hlam, p27968_0]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [h2, hlam, p27968_0]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [hlam, p27968_0]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [h26247, hlam, p27968_1]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [h2, h23339, hc34, hc45, hlam, hphi, p27968_1]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [h27576, hlam, p27968_0]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        rcases p27968_3 (m.d 0 4) (by simp) with h27979 | h27979
                                        · linarith only [h19744, h27979, hlam]
                                        · rcases p27968_3 (m.d 1 4) (by simp) with h27981 | h27981
                                          · linarith only [h26247, h27981, hlam]
                                          · rcases p27968_3 (m.d 2 4) (by simp) with h27983 | h27983
                                            · rcases p27968_3 (m.d 3 4) (by simp) with h27984 | h27984
                                              · linarith only [h27578, h27984, hlam]
                                              · rcases p27968_3 (m.d 4 5) (by simp) with h27986 | h27986
                                                · linarith only [h27580, h27986, hlam]
                                                · linarith only [h23339, h27986, hlam]
                                            · linarith only [h19744, h27983, hlam]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        rcases p27968_3 (m.d 0 4) (by simp) with h27990 | h27990
                                        · linarith only [h19744, h27990, hlam]
                                        · linarith only [h2, h27990, hlam]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [hlam, p27968_0]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [h23338, h23339, h26251, h26252, h27580, hlam, p27968_2]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [h23338, h23339, h26251, h26252, h27578, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p27968_1]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [h23337, hlam, p27968_0]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [h26251, hlam, p27968_0]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [h27578, hlam, p27968_0]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [hlam, p27968_0]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [h27581, hlam, p27968_0]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [h0, h19744, h27578, h27580, hc12, hc23, hlam, hphi, p27968_1]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [h26247, h27578, h27580, hc12, hc23, hlam, hphi, p27968_1]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [h27580, hlam, p27968_0]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        rcases p27968_3 (m.d 0 4) (by simp) with h28004 | h28004
                                        · linarith only [h23339, h28004, hlam]
                                        · linarith only [h23337, h28004, hlam]
                                      · have p27968_0 := h27968c.1
                                        have p27968_1 := h27968c.2.1
                                        have p27968_2 := h27968c.2.2.1
                                        have p27968_3 := h27968c.2.2.2
                                        linarith only [hlam, p27968_0]
                                    · linarith only [h27967, hlam, p27918_0]
                                  · linarith only [h19744, h27966, hlam]
                                · linarith only [h27965, h4, hlam]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            rcases p27918_3 (m.d 0 2) (by simp) with h28011 | h28011
                            · linarith only [h22010, h28011, hlam]
                            · linarith only [h0, h28011, hlam]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [h27579, hlam, p27918_0]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [h27580, hlam, p27918_1]
                          · have p27918_0 := h27918c.1
                            have p27918_1 := h27918c.2.1
                            have p27918_2 := h27918c.2.2.1
                            have p27918_3 := h27918c.2.2.2
                            linarith only [hlam, p27918_0]
              · linarith only [h27610, hlam, p27583_0]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [h0, hlam, p27583_0]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [hlam, p27583_0]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [h26245, hlam, p27583_1]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [h26247, hlam, p27583_1]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [h26249, hlam, p27583_1]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [h1, hlam, p27583_0]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [h1, h23338, h26252, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27583_1]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [hlam, p27583_0]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [h23338, h23339, h26247, h26252, h27578, h27580, hc12, hc23, hlam, hphi, p27583_1]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [h26252, hlam, p27583_1]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [h2, hlam, p27583_0]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [h2, h23339, h27578, h27580, hc12, hc23, hlam, hphi, p27583_1]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [h26251, hlam, p27583_1]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [hlam, p27583_0]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [h27576, hlam, p27583_1]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [h3, hlam, p27583_0]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [h23339, h27578, h27580, h3, hc12, hc23, hlam, hphi, p27583_1]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [h23338, h23339, h26251, h26252, h27578, h27580, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p27583_1]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [h23338, h23339, h26247, h26252, h27578, h27580, hc12, hc23, hlam, hphi, p27583_1]
            · have p27583_0 := h27583c.1
              have p27583_1 := h27583c.2.1
              have p27583_2 := h27583c.2.2.1
              have p27583_3 := h27583c.2.2.2
              linarith only [hlam, p27583_0]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h28038 | h28038
          · linarith only [h0, h19744, h26251, h27580, h28038, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
          · rcases h1bigk with h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c | h28040c
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [hlam, p28040_0]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              rcases p28040_3 (m.d 0 1) (by simp) with h28042 | h28042
              · rcases p28040_3 (m.d 1 2) (by simp) with h28043 | h28043
                · linarith only [h28043, hlam, p28040_0]
                · rcases p28040_3 (m.d 1 3) (by simp) with h28045 | h28045
                  · linarith only [h1, h28045, hlam]
                  · linarith only [h26245, h28045, hlam]
              · linarith only [h28042, hlam, p28040_0]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              rcases p28040_3 (m.d 0 1) (by simp) with h28049 | h28049
              · rcases p28040_3 (m.d 1 2) (by simp) with h28050 | h28050
                · linarith only [h0, h28050, hlam]
                · rcases p28040_3 (m.d 1 3) (by simp) with h28052 | h28052
                  · linarith only [h28052, hlam, p28040_0]
                  · rcases p28040_3 (m.d 1 4) (by simp) with h28054 | h28054
                    · linarith only [h2, h28054, hlam]
                    · rcases p28040_3 (m.d 1 5) (by simp) with h28056 | h28056
                      · linarith only [h28056, h3, hlam]
                      · linarith only [h26252, h28056, hlam]
              · linarith only [h28049, hlam, p28040_0]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              rcases p28040_3 (m.d 0 1) (by simp) with h28060 | h28060
              · rcases p28040_3 (m.d 1 2) (by simp) with h28061 | h28061
                · linarith only [h0, h28061, hlam]
                · rcases p28040_3 (m.d 1 3) (by simp) with h28063 | h28063
                  · linarith only [h1, h28063, hlam]
                  · linarith only [h26251, h28063, hlam]
              · linarith only [h28060, hlam, p28040_0]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              rcases p28040_3 (m.d 0 1) (by simp) with h28067 | h28067
              · rcases p28040_3 (m.d 1 2) (by simp) with h28068 | h28068
                · linarith only [h0, h28068, hlam]
                · rcases p28040_3 (m.d 1 3) (by simp) with h28070 | h28070
                  · linarith only [h1, h28070, hlam]
                  · rcases p28040_3 (m.d 1 4) (by simp) with h28072 | h28072
                    · linarith only [h2, h28072, hlam]
                    · rcases p28040_3 (m.d 1 5) (by simp) with h28074 | h28074
                      · linarith only [h28074, hlam, p28040_0]
                      · rcases h1emax with h28076 | h28076 | h28076 | h28076 | h28076
                        · linarith only [h28076, hc15, hlam, hphi, ht01, ht0b, ht5b, p28040_1]
                        · rcases h2bigk with h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c | h28078c
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [hlam, p28078_0]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [h19744, hc12, hc24, hlam, hphi, p28078_1]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [h4, hlam, p28078_0]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [h19744, hlam, p28078_0]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [h22010, hlam, p28078_0]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [h0, hlam, p28078_1]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [hlam, p28078_0]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [h26245, hlam, p28078_0]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [h26247, hlam, p28078_0]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [h26249, hlam, p28078_0]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            rcases p28078_3 (m.d 0 2) (by simp) with h28089 | h28089
                            · linarith only [h28089, hlam, p28078_0]
                            · rcases p28078_3 (m.d 1 2) (by simp) with h28091 | h28091
                              · linarith only [h26245, h28091, hlam]
                              · rcases p28078_3 (m.d 2 3) (by simp) with h28093 | h28093
                                · rcases p28078_3 (m.d 2 4) (by simp) with h28094 | h28094
                                  · linarith only [h27578, h28094, hlam]
                                  · linarith only [h19744, h28094, hlam]
                                · linarith only [h28093, hlam, p28078_0]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            rcases p28078_3 (m.d 0 2) (by simp) with h28098 | h28098
                            · linarith only [h28098, h4, hlam]
                            · linarith only [h0, h28098, hlam]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [hlam, p28078_0]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [h19744, hc02, hc23, hlam, hphi, p28078_1]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [h22010, h23338, h26251, h26252, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p28078_1]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [h0, h27580, hc12, hc45, hlam, hphi, ht23, ht34, p28078_1]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [h27580, hc12, hc45, hlam, hphi, ht23, ht34, p28078_1]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [h27578, hlam, p28078_0]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [hlam, p28078_0]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [h27580, hlam, p28078_0]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            rcases p28078_3 (m.d 0 2) (by simp) with h28109 | h28109
                            · linarith only [h28109, hlam, p28078_0]
                            · rcases p28078_3 (m.d 1 2) (by simp) with h28111 | h28111
                              · linarith only [h26249, h28111, hlam]
                              · rcases p28078_3 (m.d 2 3) (by simp) with h28113 | h28113
                                · rcases p28078_3 (m.d 2 4) (by simp) with h28114 | h28114
                                  · linarith only [h27580, h28114, hlam]
                                  · linarith only [h19744, h28114, hlam]
                                · linarith only [h28113, h4, hlam]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            rcases p28078_3 (m.d 0 2) (by simp) with h28118 | h28118
                            · linarith only [h22010, h28118, hlam]
                            · linarith only [h0, h28118, hlam]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [h27579, hlam, p28078_0]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [h0, h19744, hc12, hc25, hlam, hphi, p28078_1]
                          · have p28078_0 := h28078c.1
                            have p28078_1 := h28078c.2.1
                            have p28078_2 := h28078c.2.2.1
                            have p28078_3 := h28078c.2.2.2
                            linarith only [hlam, p28078_0]
                        · rcases h2bigk with h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c | h28124c
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [hlam, p28124_0]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [h19744, hc12, hc24, hlam, hphi, p28124_1]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [h4, hlam, p28124_0]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [h19744, hlam, p28124_0]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [h22010, hlam, p28124_0]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [h0, hlam, p28124_1]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [hlam, p28124_0]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [h26245, hlam, p28124_0]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [h26247, hlam, p28124_0]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [h26249, hlam, p28124_0]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            rcases p28124_3 (m.d 0 2) (by simp) with h28135 | h28135
                            · linarith only [h28135, hlam, p28124_0]
                            · rcases p28124_3 (m.d 1 2) (by simp) with h28137 | h28137
                              · linarith only [h26245, h28137, hlam]
                              · rcases p28124_3 (m.d 2 3) (by simp) with h28139 | h28139
                                · rcases p28124_3 (m.d 2 4) (by simp) with h28140 | h28140
                                  · linarith only [h27578, h28140, hlam]
                                  · linarith only [h19744, h28140, hlam]
                                · linarith only [h28139, hlam, p28124_0]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            rcases p28124_3 (m.d 0 2) (by simp) with h28144 | h28144
                            · linarith only [h28144, h4, hlam]
                            · linarith only [h0, h28144, hlam]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [hlam, p28124_0]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [h19744, hc02, hc23, hlam, hphi, p28124_1]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [h0, h22010, hc12, hc23, hlam, hphi, p28124_1]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [h0, h27580, hc12, hc45, hlam, hphi, ht23, ht34, p28124_1]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [h27580, hc12, hc45, hlam, hphi, ht23, ht34, p28124_1]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [h27578, hlam, p28124_0]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [hlam, p28124_0]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [h27580, hlam, p28124_0]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            rcases p28124_3 (m.d 0 2) (by simp) with h28155 | h28155
                            · linarith only [h28155, hlam, p28124_0]
                            · rcases p28124_3 (m.d 1 2) (by simp) with h28157 | h28157
                              · linarith only [h26249, h28157, hlam]
                              · rcases p28124_3 (m.d 2 3) (by simp) with h28159 | h28159
                                · rcases p28124_3 (m.d 2 4) (by simp) with h28160 | h28160
                                  · linarith only [h27580, h28160, hlam]
                                  · linarith only [h19744, h28160, hlam]
                                · linarith only [h28159, h4, hlam]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            rcases p28124_3 (m.d 0 2) (by simp) with h28164 | h28164
                            · linarith only [h22010, h28164, hlam]
                            · linarith only [h0, h28164, hlam]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [h27579, hlam, p28124_0]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [h0, h19744, hc12, hc25, hlam, hphi, p28124_1]
                          · have p28124_0 := h28124c.1
                            have p28124_1 := h28124c.2.1
                            have p28124_2 := h28124c.2.2.1
                            have p28124_3 := h28124c.2.2.2
                            linarith only [hlam, p28124_0]
                        · rcases h2bigk with h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c | h28170c
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [hlam, p28170_0]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [h19744, hc12, hc24, hlam, hphi, p28170_1]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [h4, hlam, p28170_0]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [h19744, hlam, p28170_0]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [h22010, hlam, p28170_0]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [h0, hlam, p28170_1]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [hlam, p28170_0]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [h26245, hlam, p28170_0]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [h26247, hlam, p28170_0]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [h26249, hlam, p28170_0]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            rcases p28170_3 (m.d 0 2) (by simp) with h28181 | h28181
                            · linarith only [h28181, hlam, p28170_0]
                            · rcases p28170_3 (m.d 1 2) (by simp) with h28183 | h28183
                              · linarith only [h26245, h28183, hlam]
                              · rcases p28170_3 (m.d 2 3) (by simp) with h28185 | h28185
                                · rcases p28170_3 (m.d 2 4) (by simp) with h28186 | h28186
                                  · linarith only [h27578, h28186, hlam]
                                  · linarith only [h19744, h28186, hlam]
                                · linarith only [h28185, hlam, p28170_0]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            rcases p28170_3 (m.d 0 2) (by simp) with h28190 | h28190
                            · linarith only [h28190, h4, hlam]
                            · linarith only [h0, h28190, hlam]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [hlam, p28170_0]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [h19744, hc02, hc23, hlam, hphi, p28170_1]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [h0, h22010, hc12, hc23, hlam, hphi, p28170_1]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [h0, h27580, hc12, hc45, hlam, hphi, ht23, ht34, p28170_1]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [h27580, hc12, hc45, hlam, hphi, ht23, ht34, p28170_1]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [h27578, hlam, p28170_0]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [hlam, p28170_0]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [h27580, hlam, p28170_0]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            rcases p28170_3 (m.d 0 2) (by simp) with h28201 | h28201
                            · linarith only [h28201, hlam, p28170_0]
                            · rcases p28170_3 (m.d 1 2) (by simp) with h28203 | h28203
                              · linarith only [h26249, h28203, hlam]
                              · rcases p28170_3 (m.d 2 3) (by simp) with h28205 | h28205
                                · rcases p28170_3 (m.d 2 4) (by simp) with h28206 | h28206
                                  · linarith only [h27580, h28206, hlam]
                                  · linarith only [h19744, h28206, hlam]
                                · linarith only [h28205, h4, hlam]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            rcases p28170_3 (m.d 0 2) (by simp) with h28210 | h28210
                            · linarith only [h22010, h28210, hlam]
                            · linarith only [h0, h28210, hlam]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [h27579, hlam, p28170_0]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [h0, h19744, hc12, hc25, hlam, hphi, p28170_1]
                          · have p28170_0 := h28170c.1
                            have p28170_1 := h28170c.2.1
                            have p28170_2 := h28170c.2.2.1
                            have p28170_3 := h28170c.2.2.2
                            linarith only [hlam, p28170_0]
                        · rcases h2bigk with h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c | h28216c
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [hlam, p28216_0]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [h19744, hc12, hc24, hlam, hphi, p28216_1]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [h4, hlam, p28216_0]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [h19744, hlam, p28216_0]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [h22010, hlam, p28216_0]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [h0, hlam, p28216_1]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [hlam, p28216_0]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [h26245, hlam, p28216_0]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [h26247, hlam, p28216_0]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [h26249, hlam, p28216_0]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            rcases p28216_3 (m.d 0 2) (by simp) with h28227 | h28227
                            · linarith only [h28227, hlam, p28216_0]
                            · rcases p28216_3 (m.d 1 2) (by simp) with h28229 | h28229
                              · linarith only [h26245, h28229, hlam]
                              · rcases p28216_3 (m.d 2 3) (by simp) with h28231 | h28231
                                · rcases p28216_3 (m.d 2 4) (by simp) with h28232 | h28232
                                  · linarith only [h27578, h28232, hlam]
                                  · linarith only [h19744, h28232, hlam]
                                · linarith only [h28231, hlam, p28216_0]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            rcases p28216_3 (m.d 0 2) (by simp) with h28236 | h28236
                            · linarith only [h28236, h4, hlam]
                            · linarith only [h0, h28236, hlam]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [hlam, p28216_0]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [h19744, hc02, hc23, hlam, hphi, p28216_1]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [h0, h22010, hc12, hc23, hlam, hphi, p28216_1]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [h0, h27580, hc12, hc45, hlam, hphi, ht23, ht34, p28216_1]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [h27580, hc12, hc45, hlam, hphi, ht23, ht34, p28216_1]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [h27578, hlam, p28216_0]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [hlam, p28216_0]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [h27580, hlam, p28216_0]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            rcases p28216_3 (m.d 0 2) (by simp) with h28247 | h28247
                            · linarith only [h28247, hlam, p28216_0]
                            · rcases p28216_3 (m.d 1 2) (by simp) with h28249 | h28249
                              · linarith only [h26249, h28249, hlam]
                              · rcases p28216_3 (m.d 2 3) (by simp) with h28251 | h28251
                                · rcases p28216_3 (m.d 2 4) (by simp) with h28252 | h28252
                                  · linarith only [h27580, h28252, hlam]
                                  · linarith only [h19744, h28252, hlam]
                                · linarith only [h28251, h4, hlam]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            rcases p28216_3 (m.d 0 2) (by simp) with h28256 | h28256
                            · linarith only [h22010, h28256, hlam]
                            · linarith only [h0, h28256, hlam]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [h27579, hlam, p28216_0]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [h0, h19744, hc12, hc25, hlam, hphi, p28216_1]
                          · have p28216_0 := h28216c.1
                            have p28216_1 := h28216c.2.1
                            have p28216_2 := h28216c.2.2.1
                            have p28216_3 := h28216c.2.2.2
                            linarith only [hlam, p28216_0]
              · linarith only [h28067, hlam, p28040_0]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [h0, hlam, p28040_0]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [hlam, p28040_0]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [h26245, hlam, p28040_1]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [h26247, hlam, p28040_1]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [h26249, hlam, p28040_1]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [h1, hlam, p28040_0]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [h26252, hc12, hc35, hlam, hphi, ht23, p28040_1]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [hlam, p28040_0]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [h23338, h26247, h26252, h4, hc12, hc23, hlam, hphi, p28040_1]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [h26252, hlam, p28040_1]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [h2, hlam, p28040_0]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [h2, h23339, hc12, hc45, hlam, hphi, ht23, ht34, p28040_1]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [h26251, hlam, p28040_1]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [hlam, p28040_0]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [h27576, hlam, p28040_1]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [h3, hlam, p28040_0]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [h23338, h26252, h4, hc12, hc23, hlam, hphi, p28040_1]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [h23338, h26245, h26252, h4, hc12, hc23, hlam, hphi, p28040_1]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [h23338, h26247, h26252, h4, hc12, hc23, hlam, hphi, p28040_1]
            · have p28040_0 := h28040c.1
              have p28040_1 := h28040c.2.1
              have p28040_2 := h28040c.2.2.1
              have p28040_3 := h28040c.2.2.2
              linarith only [hlam, p28040_0]
      · linarith only [h23338, h27579, h4, hlam]
    · linarith only [h1, h23338, h26251, h26252, h27578, h4, hc01, hc15, hlam, hphi, ht0b, ht5b]

set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h26247 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h26249 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h26251 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  rcases m.htr 1 3 5 (by decide) (by decide) with h26252 | h26252
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245 h26247 h26249 h26251 h26252
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 h23339 h26245 h26247 h26249 h26251 h26252

end R2N4
