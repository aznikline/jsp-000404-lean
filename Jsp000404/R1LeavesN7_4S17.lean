import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 22768000 in
set_option maxHeartbeats 22768000 in
theorem r1l7_11_23_L_I_H_I_s0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_23_L_I_H_I_s1 m hb1 hb3 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h10577 | h10577
    · rcases m.htr 0 1 5 (by decide) (by decide) with h10578 | h10578
      · rcases m.htr 0 2 3 (by decide) (by decide) with h10579 | h10579
        · linarith only [h0, h1, h10579, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h10581 | h10581
          · rcases m.htr 0 3 4 (by decide) (by decide) with h10582 | h10582
            · rcases m.htr 0 3 5 (by decide) (by decide) with h10583 | h10583
              · rcases m.htr 0 4 5 (by decide) (by decide) with h10584 | h10584
                · rcases m.htr 1 2 3 (by decide) (by decide) with h10585 | h10585
                  · linarith only [h0, h1, h10579, h10581, h10585, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h10587 | h10587
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10588 | h10588
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h10589 | h10589
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h10590 | h10590
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h10591 | h10591
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h10592 | h10592
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h10593 | h10593
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h10594 | h10594
                                  · linarith only [h0, h1, h10585, h10587, h10594, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · linarith only [h0, h1, h10585, h10587, h10591, h10594, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h1, h10585, h10593, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h10585, h10592, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h10599 | h10599
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h10600 | h10600
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h10601 | h10601
                                  · linarith only [h10587, h10591, h10601, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h10603 | h10603
                                    · linarith only [h10587, h10591, h10599, h10603, hlam]
                                    · rcases h1bigk with h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c | h10605c
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [hlam, p10605_0]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [h1, h10585, hc12, hc23, hlam, hphi, p10605_1]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [h1, hlam, p10605_0]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        rcases p10605_3 (m.d 0 1) (by simp) with h10609 | h10609
                                        · rcases p10605_3 (m.d 1 2) (by simp) with h10610 | h10610
                                          · linarith only [h0, h10610, hlam]
                                          · linarith only [h10587, h10610, hlam]
                                        · linarith only [h10609, hlam, p10605_0]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        rcases p10605_3 (m.d 0 1) (by simp) with h10614 | h10614
                                        · rcases p10605_3 (m.d 1 2) (by simp) with h10615 | h10615
                                          · linarith only [h0, h10615, hlam]
                                          · linarith only [h10588, h10615, hlam]
                                        · linarith only [h10614, hlam, p10605_0]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [h0, hlam, p10605_0]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [hlam, p10605_0]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [h10585, hlam, p10605_0]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [h0, h1, h10585, h10587, h10599, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10605_1]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [h0, h1, h10585, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10605_1]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [h0, h10585, hc12, hc23, hlam, hphi, p10605_1]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        rcases p10605_3 (m.d 0 1) (by simp) with h10625 | h10625
                                        · linarith only [h1, h10625, hlam]
                                        · linarith only [h0, h10625, hlam]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [hlam, p10605_0]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [h0, h1, h10581, h10584, h10591, hlam, p10605_2]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        rcases p10605_3 (m.d 0 1) (by simp) with h10630 | h10630
                                        · linarith only [h1, h10630, hlam]
                                        · linarith only [h10578, h10630, hlam]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [h10577, hlam, p10605_0]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [h10587, hlam, p10605_1]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [h10589, hlam, p10605_0]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [hlam, p10605_0]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [h10591, hlam, p10605_1]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [h10578, hlam, p10605_0]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [h10588, hlam, p10605_1]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [h10590, hlam, p10605_0]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [h1, h10578, h10587, h10599, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10605_1]
                                      · have p10605_0 := h10605c.1
                                        have p10605_1 := h10605c.2.1
                                        have p10605_2 := h10605c.2.2.1
                                        have p10605_3 := h10605c.2.2.2
                                        linarith only [hlam, p10605_0]
                                · linarith only [h0, h1, h10585, h10600, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h10581, h10584, h10585, h10587, h10591, h10599, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h10587, h10590, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h10582, h10587, h10589, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h10647 | h10647
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h10648 | h10648
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h10649 | h10649
                            · linarith only [h10587, h10588, h10649, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h10651 | h10651
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h10652 | h10652
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h10653 | h10653
                                  · linarith only [h10587, h10588, h10649, h10653, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h0, h1, h10581, h10584, h10585, h10588, h10653, hc12, hc23, hlam, hphi]
                                · linarith only [h0, h1, h10581, h10584, h10585, h10648, h10649, h10652, hlam]
                              · linarith only [h0, h1, h10585, h10651, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h10578, h10587, h10588, h10648, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h1, h10578, h10587, h10588, h10647, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h10581, h10585, h10587, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h10661 | h10661
                  · linarith only [h0, h1, h10579, h10661, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h10663 | h10663
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10664 | h10664
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h10665 | h10665
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h10666 | h10666
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h10667 | h10667
                            · linarith only [h10577, h10584, h10667, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h10669 | h10669
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h10670 | h10670
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h10671 | h10671
                                  · linarith only [h0, h1, h10584, h10661, h10663, h10671, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h10673 | h10673
                                    · linarith only [h10582, h10584, h10673, hlam]
                                    · rcases h1bigk with h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c | h10675c
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [hlam, p10675_0]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [h1, h10661, hc12, hc23, hlam, hphi, p10675_1]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [h1, hlam, p10675_0]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        rcases p10675_3 (m.d 0 1) (by simp) with h10679 | h10679
                                        · rcases p10675_3 (m.d 1 2) (by simp) with h10680 | h10680
                                          · linarith only [h0, h10680, hlam]
                                          · linarith only [h10663, h10680, hlam]
                                        · linarith only [h10679, hlam, p10675_0]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        rcases p10675_3 (m.d 0 1) (by simp) with h10684 | h10684
                                        · rcases p10675_3 (m.d 1 2) (by simp) with h10685 | h10685
                                          · linarith only [h0, h10685, hlam]
                                          · linarith only [h10664, h10685, hlam]
                                        · linarith only [h10684, hlam, p10675_0]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [h0, hlam, p10675_0]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [hlam, p10675_0]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [h10661, hlam, p10675_0]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [h0, h1, h10661, h10663, h10669, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10675_1]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [h0, h1, h10661, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10675_1]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [h0, h10661, hc12, hc23, hlam, hphi, p10675_1]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        rcases p10675_3 (m.d 0 1) (by simp) with h10695 | h10695
                                        · linarith only [h1, h10695, hlam]
                                        · linarith only [h0, h10695, hlam]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [hlam, p10675_0]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        rcases p10675_3 (m.d 0 1) (by simp) with h10699 | h10699
                                        · linarith only [h1, h10699, hlam]
                                        · linarith only [h10577, h10699, hlam]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        rcases p10675_3 (m.d 0 1) (by simp) with h10702 | h10702
                                        · linarith only [h1, h10702, hlam]
                                        · linarith only [h10578, h10702, hlam]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [h10577, hlam, p10675_0]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [h10663, hlam, p10675_1]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [h10665, hlam, p10675_0]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [hlam, p10675_0]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [h10667, hlam, p10675_1]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [h10578, hlam, p10675_0]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [h10664, hlam, p10675_1]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [h10666, hlam, p10675_0]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [h1, h10578, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p10675_1]
                                      · have p10675_0 := h10675c.1
                                        have p10675_1 := h10675c.2.1
                                        have p10675_2 := h10675c.2.2.1
                                        have p10675_3 := h10675c.2.2.2
                                        linarith only [hlam, p10675_0]
                                · linarith only [h0, h1, h10661, h10670, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h10661, h10663, h10669, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h10663, h10666, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h10663, h10665, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h10719 | h10719
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h10720 | h10720
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h10721 | h10721
                            · linarith only [h1, h10577, h10578, h10584, h10663, h10664, h10721, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h10723 | h10723
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h10724 | h10724
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h10725 | h10725
                                  · linarith only [h0, h1, h10581, h10584, h10725, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h10727 | h10727
                                    · linarith only [h10663, h10664, h10723, h10725, h10727, hlam]
                                    · rcases h1bigk with h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c | h10729c
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [hlam, p10729_0]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [h1, h10661, h10663, h10723, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10729_1]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [h1, hlam, p10729_0]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        rcases p10729_3 (m.d 0 1) (by simp) with h10733 | h10733
                                        · rcases p10729_3 (m.d 1 2) (by simp) with h10734 | h10734
                                          · linarith only [h0, h10734, hlam]
                                          · linarith only [h10663, h10734, hlam]
                                        · linarith only [h10733, hlam, p10729_0]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [h1, h10661, h10663, h10664, h10723, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10729_1]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [h0, hlam, p10729_0]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [hlam, p10729_0]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [h10661, hlam, p10729_0]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [h10663, h10664, h10723, h10725, hc34, hc45, hlam, hphi, p10729_1]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [h10664, hlam, p10729_0]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [h0, h10661, hc12, hc23, hlam, hphi, p10729_1]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        rcases p10729_3 (m.d 0 1) (by simp) with h10745 | h10745
                                        · linarith only [h1, h10745, hlam]
                                        · linarith only [h0, h10745, hlam]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [hlam, p10729_0]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        rcases p10729_3 (m.d 0 1) (by simp) with h10749 | h10749
                                        · linarith only [h1, h10749, hlam]
                                        · linarith only [h10577, h10749, hlam]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        rcases p10729_3 (m.d 0 1) (by simp) with h10752 | h10752
                                        · linarith only [h1, h10752, hlam]
                                        · linarith only [h10578, h10752, hlam]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [h10577, hlam, p10729_0]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [h10663, hlam, p10729_1]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [h10719, hlam, p10729_0]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [hlam, p10729_0]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [h10721, hlam, p10729_1]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [h10578, hlam, p10729_0]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [h10578, h10663, h10723, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10729_1]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [h10720, hlam, p10729_0]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [h1, h10578, h10661, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10729_1]
                                      · have p10729_0 := h10729c.1
                                        have p10729_1 := h10729c.2.1
                                        have p10729_2 := h10729c.2.2.1
                                        have p10729_3 := h10729c.2.2.2
                                        linarith only [hlam, p10729_0]
                                · linarith only [h0, h1, h10661, h10663, h10723, h10724, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h1, h10578, h10661, h10663, h10664, h10723, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1, h10578, h10663, h10664, h10720, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h1, h10578, h10663, h10664, h10719, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h10581, h10661, h10663, hc12, hc23, hlam, hphi]
              · linarith only [h1, h10578, h10583, hlam]
            · linarith only [h1, h10577, h10582, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h10772 | h10772
            · rcases m.htr 0 3 5 (by decide) (by decide) with h10773 | h10773
              · rcases m.htr 0 4 5 (by decide) (by decide) with h10774 | h10774
                · rcases m.htr 1 2 3 (by decide) (by decide) with h10775 | h10775
                  · linarith only [h0, h1, h10579, h10775, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h10777 | h10777
                    · linarith only [h0, h1, h10581, h10774, h10775, h10777, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10779 | h10779
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h10780 | h10780
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h10781 | h10781
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h10782 | h10782
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h10783 | h10783
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h10784 | h10784
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h10785 | h10785
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h10786 | h10786
                                    · rcases h1bigk with h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c | h10787c
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [hlam, p10787_0]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [h1, h10775, h10779, h10784, h10786, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10787_1]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [h1, hlam, p10787_0]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [h1, h10775, h10777, h10779, h10784, h10786, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10787_1]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        rcases p10787_3 (m.d 0 1) (by simp) with h10792 | h10792
                                        · rcases p10787_3 (m.d 1 2) (by simp) with h10793 | h10793
                                          · linarith only [h0, h10793, hlam]
                                          · linarith only [h10779, h10793, hlam]
                                        · linarith only [h10792, hlam, p10787_0]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [h0, hlam, p10787_0]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [hlam, p10787_0]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [h10775, hlam, p10787_0]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [h10777, hlam, p10787_0]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [h0, h1, h10775, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10787_1]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [h0, h10775, hc12, hc23, hlam, hphi, p10787_1]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        rcases p10787_3 (m.d 0 1) (by simp) with h10803 | h10803
                                        · linarith only [h1, h10803, hlam]
                                        · linarith only [h0, h10803, hlam]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [hlam, p10787_0]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        rcases p10787_3 (m.d 0 1) (by simp) with h10807 | h10807
                                        · linarith only [h1, h10807, hlam]
                                        · linarith only [h10577, h10807, hlam]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        rcases p10787_3 (m.d 0 1) (by simp) with h10810 | h10810
                                        · linarith only [h1, h10810, hlam]
                                        · linarith only [h10578, h10810, hlam]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [h10577, hlam, p10787_0]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [h10577, h10779, h10784, h10786, hc01, hc45, hlam, hphi, ht0b, ht5b, p10787_1]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [h10780, hlam, p10787_0]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [hlam, p10787_0]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [h1, h10577, h10775, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10787_1]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [h10578, hlam, p10787_0]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [h10779, hlam, p10787_1]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [h10781, hlam, p10787_0]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [h10782, hlam, p10787_0]
                                      · have p10787_0 := h10787c.1
                                        have p10787_1 := h10787c.2.1
                                        have p10787_2 := h10787c.2.2.1
                                        have p10787_3 := h10787c.2.2.2
                                        linarith only [hlam, p10787_0]
                                    · linarith only [h1, h10577, h10775, h10782, h10786, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h1, h10578, h10581, h10775, h10782, h10785, hc02, hc23, hlam, hphi]
                                · linarith only [h1, h10577, h10775, h10782, h10784, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h10577, h10775, h10777, h10779, h10783, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1, h10577, h10774, h10777, h10779, h10782, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h0, h1, h10779, h10781, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h1, h10779, h10780, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h10830 | h10830
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h10831 | h10831
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h10832 | h10832
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h10833 | h10833
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h10834 | h10834
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h10835 | h10835
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h10836 | h10836
                                    · rcases h1bigk with h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [hlam, p10837_0]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [h1, h10775, hc12, hc23, hlam, hphi, p10837_1]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [h1, hlam, p10837_0]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [h1, h10775, h10830, h10836, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10837_1]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [h1, h10775, h10779, hc12, hc23, hlam, hphi, p10837_1]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [h0, hlam, p10837_0]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [hlam, p10837_0]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [h10775, hlam, p10837_0]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [h10777, hlam, p10837_0]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [h10779, hlam, p10837_0]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [h0, h10775, hc12, hc23, hlam, hphi, p10837_1]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        rcases p10837_3 (m.d 0 1) (by simp) with h10849 | h10849
                                        · linarith only [h1, h10849, hlam]
                                        · linarith only [h0, h10849, hlam]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [hlam, p10837_0]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        rcases p10837_3 (m.d 0 1) (by simp) with h10853 | h10853
                                        · linarith only [h1, h10853, hlam]
                                        · linarith only [h10577, h10853, hlam]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        rcases p10837_3 (m.d 0 1) (by simp) with h10856 | h10856
                                        · linarith only [h1, h10856, hlam]
                                        · linarith only [h10578, h10856, hlam]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [h10577, hlam, p10837_0]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [h1, h10577, h10775, hc12, hc23, hlam, hphi, p10837_1]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [h10830, hlam, p10837_0]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [hlam, p10837_0]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [h1, h10577, h10775, h10779, hc12, hc23, hlam, hphi, p10837_1]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [h10578, hlam, p10837_0]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [h1, h10578, h10775, hc12, hc23, hlam, hphi, p10837_1]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [h10831, hlam, p10837_0]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [h10832, hlam, p10837_0]
                                      · have p10837_0 := h10837c.1
                                        have p10837_1 := h10837c.2.1
                                        have p10837_2 := h10837c.2.2.1
                                        have p10837_3 := h10837c.2.2.2
                                        linarith only [hlam, p10837_0]
                                    · linarith only [h1, h10577, h10775, h10832, h10836, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h1, h10577, h10775, h10832, h10835, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h1, h10577, h10775, h10832, h10834, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h10577, h10775, h10832, h10833, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1, h10577, h10774, h10775, h10777, h10832, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h10831, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h10830, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h10876 | h10876
                  · linarith only [h0, h1, h10579, h10773, h10876, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h10878 | h10878
                    · linarith only [h0, h1, h10581, h10876, h10878, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10880 | h10880
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h10881 | h10881
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h10882 | h10882
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h10883 | h10883
                            · linarith only [h1, h10577, h10774, h10876, h10883, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h10878, h10880, h10883, hlam]
                          · linarith only [h0, h1, h10880, h10882, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1, h10577, h10878, h10880, h10881, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h10888 | h10888
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h10889 | h10889
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h10890 | h10890
                            · linarith only [h1, h10577, h10581, h10774, h10890, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h10892 | h10892
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h10893 | h10893
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h10894 | h10894
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h10895 | h10895
                                    · linarith only [h10577, h10774, h10888, h10895, hlam]
                                    · rcases h1bigk with h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c | h10897c
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [hlam, p10897_0]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [h1, h10876, hc12, hc23, hlam, hphi, p10897_1]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [h1, hlam, p10897_0]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [h1, h10876, h10878, hc12, hc23, hlam, hphi, p10897_1]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [h1, h10876, h10880, hc12, hc23, hlam, hphi, p10897_1]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [h0, hlam, p10897_0]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [hlam, p10897_0]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [h10876, hlam, p10897_0]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [h10878, hlam, p10897_0]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [h10880, hlam, p10897_0]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [h0, h10876, hc12, hc23, hlam, hphi, p10897_1]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        rcases p10897_3 (m.d 0 1) (by simp) with h10909 | h10909
                                        · linarith only [h1, h10909, hlam]
                                        · linarith only [h0, h10909, hlam]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [hlam, p10897_0]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        rcases p10897_3 (m.d 0 1) (by simp) with h10913 | h10913
                                        · linarith only [h1, h10913, hlam]
                                        · linarith only [h10577, h10913, hlam]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        rcases p10897_3 (m.d 0 1) (by simp) with h10916 | h10916
                                        · linarith only [h1, h10916, hlam]
                                        · linarith only [h10578, h10916, hlam]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [h10577, hlam, p10897_0]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [h1, h10578, h10876, h10890, hc12, hc23, hlam, hphi, p10897_1]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [h10888, hlam, p10897_0]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [hlam, p10897_0]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [h10890, hlam, p10897_1]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [h10578, hlam, p10897_0]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [h1, h10578, h10876, hc12, hc23, hlam, hphi, p10897_1]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [h10889, hlam, p10897_0]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [h1, h10578, h10876, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10897_1]
                                      · have p10897_0 := h10897c.1
                                        have p10897_1 := h10897c.2.1
                                        have p10897_2 := h10897c.2.2.1
                                        have p10897_3 := h10897c.2.2.2
                                        linarith only [hlam, p10897_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h10929 | h10929
                                    · linarith only [h0, h10581, h10894, h10929, hc12, hc34, hlam, hphi, ht23]
                                    · rcases h1bigk with h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c | h10931c
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [hlam, p10931_0]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [h1, h10876, hc12, hc23, hlam, hphi, p10931_1]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [h1, hlam, p10931_0]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [h1, h10876, h10878, hc12, hc23, hlam, hphi, p10931_1]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [h1, h10876, h10880, hc12, hc23, hlam, hphi, p10931_1]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [h0, hlam, p10931_0]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [hlam, p10931_0]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [h10876, hlam, p10931_0]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [h10878, hlam, p10931_0]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [h10880, hlam, p10931_0]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [h0, h10876, hc12, hc23, hlam, hphi, p10931_1]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        rcases p10931_3 (m.d 0 1) (by simp) with h10943 | h10943
                                        · linarith only [h1, h10943, hlam]
                                        · linarith only [h0, h10943, hlam]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [hlam, p10931_0]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        rcases p10931_3 (m.d 0 1) (by simp) with h10947 | h10947
                                        · linarith only [h1, h10947, hlam]
                                        · linarith only [h10577, h10947, hlam]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        rcases p10931_3 (m.d 0 1) (by simp) with h10950 | h10950
                                        · linarith only [h1, h10950, hlam]
                                        · linarith only [h10578, h10950, hlam]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [h10577, hlam, p10931_0]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [h1, h10577, h10876, hc12, hc23, hlam, hphi, p10931_1]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [h10888, hlam, p10931_0]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [hlam, p10931_0]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [h10890, hlam, p10931_1]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [h10578, hlam, p10931_0]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [h1, h10578, h10876, hc12, hc23, hlam, hphi, p10931_1]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [h10889, hlam, p10931_0]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [h1, h10578, h10876, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10931_1]
                                      · have p10931_0 := h10931c.1
                                        have p10931_1 := h10931c.2.1
                                        have p10931_2 := h10931c.2.2.1
                                        have p10931_3 := h10931c.2.2.2
                                        linarith only [hlam, p10931_0]
                                · linarith only [h1, h10578, h10876, h10889, h10893, hlam]
                              · linarith only [h0, h1, h10876, h10892, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h10577, h10878, h10889, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h10577, h10878, h10888, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h10578, h10773, hlam]
            · linarith only [h1, h10577, h10772, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h10969 | h10969
        · linarith only [h0, h1, h10969, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h10971 | h10971
          · rcases m.htr 0 3 4 (by decide) (by decide) with h10972 | h10972
            · rcases m.htr 0 3 5 (by decide) (by decide) with h10973 | h10973
              · rcases m.htr 0 4 5 (by decide) (by decide) with h10974 | h10974
                · linarith only [h0, h10578, h10971, h10974, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h10976 | h10976
                  · linarith only [h0, h1, h10969, h10976, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h10978 | h10978
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10979 | h10979
                      · linarith only [h0, h10578, h10979, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h10981 | h10981
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h10982 | h10982
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h10983 | h10983
                            · linarith only [h0, h10577, h10578, h10971, h10974, h10983, hlam]
                            · linarith only [h0, h10578, h10978, h10983, hc24, hc45, hlam, hphi]
                          · linarith only [h0, h1, h10978, h10982, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h10978, h10981, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h10971, h10976, h10978, hc12, hc23, hlam, hphi]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h10989 | h10989
                · linarith only [h0, h1, h10971, h10973, h10989, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h10991 | h10991
                  · linarith only [h0, h1, h10973, h10991, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h10993 | h10993
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10994 | h10994
                      · linarith only [h0, h10578, h10994, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h10996 | h10996
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h10997 | h10997
                          · linarith only [h0, h1, h10973, h10991, h10997, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h10993, h10997, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h10993, h10996, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h10969, h10971, h10993, hc12, hc23, hlam, hphi]
            · linarith only [h1, h10577, h10972, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h11003 | h11003
            · rcases m.htr 0 3 5 (by decide) (by decide) with h11004 | h11004
              · rcases m.htr 0 4 5 (by decide) (by decide) with h11005 | h11005
                · linarith only [h10577, h10578, h11005, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11007 | h11007
                  · linarith only [h0, h1, h10969, h11007, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11009 | h11009
                    · linarith only [h0, h10971, h11009, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11011 | h11011
                      · linarith only [h0, h10578, h11011, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11013 | h11013
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11014 | h11014
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11015 | h11015
                            · linarith only [h10577, h10578, h10971, h11005, h11007, h11014, h11015, hc02, hc23, hlam, hphi]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11017 | h11017
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h11018 | h11018
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h11019 | h11019
                                  · linarith only [h0, h10578, h11015, h11019, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11021 | h11021
                                    · linarith only [h10577, h10578, h11013, h11014, h11019, h11021, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · rcases h1bigk with h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c | h11023c
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [hlam, p11023_0]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [h10578, h11011, h11019, hc12, hc45, hlam, hphi, ht23, ht34, p11023_1]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [h1, hlam, p11023_0]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [h10578, h11011, h11019, hc14, hc45, hlam, hphi, p11023_1]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [h10578, hlam, p11023_0]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [h0, hlam, p11023_0]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [hlam, p11023_0]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [h11007, hlam, p11023_0]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [h11009, hlam, p11023_0]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [h11011, hlam, p11023_0]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [h0, h11007, hc12, hc23, hlam, hphi, p11023_1]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        rcases p11023_3 (m.d 0 1) (by simp) with h11035 | h11035
                                        · linarith only [h1, h11035, hlam]
                                        · linarith only [h0, h11035, hlam]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [hlam, p11023_0]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        rcases p11023_3 (m.d 0 1) (by simp) with h11039 | h11039
                                        · linarith only [h1, h11039, hlam]
                                        · linarith only [h10577, h11039, hlam]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [h10577, h10578, h11007, h11009, hc12, hc23, hlam, hphi, p11023_1]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [h10577, hlam, p11023_0]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [h10577, h10578, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11023_1]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [h11013, hlam, p11023_0]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [hlam, p11023_0]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [h11015, hlam, p11023_1]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [h10577, h11011, h11019, hc14, hc45, hlam, hphi, p11023_1]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        rcases p11023_3 (m.d 0 1) (by simp) with h11049 | h11049
                                        · linarith only [h10578, h11049, hlam]
                                        · linarith only [h0, h11049, hlam]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [h11014, hlam, p11023_0]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        rcases p11023_3 (m.d 0 1) (by simp) with h11053 | h11053
                                        · linarith only [h10578, h11053, hlam]
                                        · linarith only [h10577, h11053, hlam]
                                      · have p11023_0 := h11023c.1
                                        have p11023_1 := h11023c.2.1
                                        have p11023_2 := h11023c.2.2.1
                                        have p11023_3 := h11023c.2.2.2
                                        linarith only [hlam, p11023_0]
                                · linarith only [h1, h11004, h11007, h11018, hlam]
                              · linarith only [h1, h10577, h11007, h11009, h11017, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h11004, h11014, hlam]
                        · linarith only [h1, h10577, h11009, h11013, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h11061 | h11061
                · linarith only [h10577, h10578, h11061, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11063 | h11063
                  · linarith only [h0, h1, h11004, h11063, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11065 | h11065
                    · linarith only [h0, h1, h10971, h11004, h11065, hc02, hc35, hlam, hphi, ht23]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11067 | h11067
                      · linarith only [h0, h10578, h11067, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11069 | h11069
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11070 | h11070
                          · linarith only [h1, h10577, h11004, h11063, h11065, h11070, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h10577, h11065, h11070, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h10577, h11065, h11069, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h10577, h11003, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h11075 | h11075
      · rcases m.htr 0 2 3 (by decide) (by decide) with h11076 | h11076
        · linarith only [h0, h1, h11076, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h11078 | h11078
          · linarith only [h0, h10577, h11078, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h11080 | h11080
            · rcases m.htr 0 3 5 (by decide) (by decide) with h11081 | h11081
              · rcases m.htr 0 4 5 (by decide) (by decide) with h11082 | h11082
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11083 | h11083
                  · linarith only [h0, h1, h11076, h11083, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11085 | h11085
                    · linarith only [h0, h10577, h11078, h11085, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11087 | h11087
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11088 | h11088
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11089 | h11089
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11090 | h11090
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11091 | h11091
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h11092 | h11092
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h11093 | h11093
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11094 | h11094
                                    · rcases h1bigk with h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c | h11095c
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [hlam, p11095_0]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [h10577, h11083, h11088, hc12, hc23, hlam, hphi, p11095_1]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [h1, hlam, p11095_0]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [h10577, hlam, p11095_0]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        rcases p11095_3 (m.d 0 1) (by simp) with h11100 | h11100
                                        · rcases p11095_3 (m.d 1 2) (by simp) with h11101 | h11101
                                          · linarith only [h0, h11101, hlam]
                                          · linarith only [h11087, h11101, hlam]
                                        · linarith only [h11100, hlam, p11095_0]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [h0, hlam, p11095_0]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [hlam, p11095_0]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [h11083, hlam, p11095_0]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [h11085, hlam, p11095_0]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [h0, h10577, h11083, h11088, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p11095_1]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [h0, h11083, hc12, hc23, hlam, hphi, p11095_1]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        rcases p11095_3 (m.d 0 1) (by simp) with h11111 | h11111
                                        · linarith only [h1, h11111, hlam]
                                        · linarith only [h0, h11111, hlam]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [hlam, p11095_0]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [h0, h10577, h11083, h11087, h11092, h11094, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11095_1]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        rcases p11095_3 (m.d 0 1) (by simp) with h11116 | h11116
                                        · linarith only [h1, h11116, hlam]
                                        · linarith only [h11075, h11116, hlam]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [h0, h11087, h11092, h11094, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p11095_1]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        rcases p11095_3 (m.d 0 1) (by simp) with h11120 | h11120
                                        · linarith only [h10577, h11120, hlam]
                                        · linarith only [h0, h11120, hlam]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [h11088, hlam, p11095_0]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [hlam, p11095_0]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        rcases p11095_3 (m.d 0 1) (by simp) with h11125 | h11125
                                        · linarith only [h10577, h11125, hlam]
                                        · linarith only [h11075, h11125, hlam]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [h11075, hlam, p11095_0]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [h11087, hlam, p11095_1]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [h11089, hlam, p11095_0]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [h11090, hlam, p11095_0]
                                      · have p11095_0 := h11095c.1
                                        have p11095_1 := h11095c.2.1
                                        have p11095_2 := h11095c.2.2.1
                                        have p11095_3 := h11095c.2.2.2
                                        linarith only [hlam, p11095_0]
                                    · linarith only [h0, h10577, h11083, h11087, h11088, h11093, h11094, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h10577, h11075, h11078, h11088, h11090, h11093, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                · linarith only [h0, h10577, h11083, h11087, h11088, h11092, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h0, h10577, h11083, h11087, h11088, h11091, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h0, h10577, h11087, h11090, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h0, h10577, h11087, h11088, h11089, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h1, h11080, h11087, h11088, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11140 | h11140
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11141 | h11141
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11142 | h11142
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11143 | h11143
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h11144 | h11144
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h11145 | h11145
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11146 | h11146
                                    · rcases h1bigk with h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c | h11147c
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [hlam, p11147_0]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [h10577, h11085, hc12, hc24, hlam, hphi, p11147_1]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [h1, hlam, p11147_0]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [h10577, hlam, p11147_0]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [h10577, h11085, h11087, hc12, hc24, hlam, hphi, p11147_1]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [h0, hlam, p11147_0]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [hlam, p11147_0]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [h11083, hlam, p11147_0]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [h11085, hlam, p11147_0]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [h11087, hlam, p11147_0]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [h0, h11083, hc12, hc23, hlam, hphi, p11147_1]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        rcases p11147_3 (m.d 0 1) (by simp) with h11159 | h11159
                                        · linarith only [h1, h11159, hlam]
                                        · linarith only [h0, h11159, hlam]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [hlam, p11147_0]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [h10577, h11075, h11083, h11087, hc12, hc23, hlam, hphi, p11147_1]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        rcases p11147_3 (m.d 0 1) (by simp) with h11164 | h11164
                                        · linarith only [h1, h11164, hlam]
                                        · linarith only [h11075, h11164, hlam]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [h11075, h11085, h11087, h11143, hc12, hc23, hlam, hphi, p11147_1]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        rcases p11147_3 (m.d 0 1) (by simp) with h11168 | h11168
                                        · linarith only [h10577, h11168, hlam]
                                        · linarith only [h0, h11168, hlam]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [h11140, hlam, p11147_0]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [hlam, p11147_0]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        rcases p11147_3 (m.d 0 1) (by simp) with h11173 | h11173
                                        · linarith only [h10577, h11173, hlam]
                                        · linarith only [h11075, h11173, hlam]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [h11075, hlam, p11147_0]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [h1, h11075, h11083, hc12, hc23, hlam, hphi, p11147_1]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [h11141, hlam, p11147_0]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [h11142, hlam, p11147_0]
                                      · have p11147_0 := h11147c.1
                                        have p11147_1 := h11147c.2.1
                                        have p11147_2 := h11147c.2.2.1
                                        have p11147_3 := h11147c.2.2.2
                                        linarith only [hlam, p11147_0]
                                    · rcases h1bigk with h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c | h11181c
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [hlam, p11181_0]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [h10577, h11085, h11143, hc12, hc23, hlam, hphi, p11181_1]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [h1, hlam, p11181_0]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [h10577, hlam, p11181_0]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [h10577, h11085, h11087, h11143, hc12, hc23, hlam, hphi, p11181_1]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [h0, hlam, p11181_0]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [hlam, p11181_0]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [h11083, hlam, p11181_0]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [h11085, hlam, p11181_0]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [h11087, hlam, p11181_0]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [h0, h11083, hc12, hc23, hlam, hphi, p11181_1]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        rcases p11181_3 (m.d 0 1) (by simp) with h11193 | h11193
                                        · linarith only [h1, h11193, hlam]
                                        · linarith only [h0, h11193, hlam]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [hlam, p11181_0]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [h10577, h11075, h11083, h11142, h11146, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11181_1]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        rcases p11181_3 (m.d 0 1) (by simp) with h11198 | h11198
                                        · linarith only [h1, h11198, hlam]
                                        · linarith only [h11075, h11198, hlam]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [h11075, h11142, h11146, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11181_1]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        rcases p11181_3 (m.d 0 1) (by simp) with h11202 | h11202
                                        · linarith only [h10577, h11202, hlam]
                                        · linarith only [h0, h11202, hlam]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [h11140, hlam, p11181_0]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [hlam, p11181_0]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        rcases p11181_3 (m.d 0 1) (by simp) with h11207 | h11207
                                        · linarith only [h10577, h11207, hlam]
                                        · linarith only [h11075, h11207, hlam]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [h11075, hlam, p11181_0]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [h1, h11075, h11083, hc12, hc23, hlam, hphi, p11181_1]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [h11141, hlam, p11181_0]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [h11142, hlam, p11181_0]
                                      · have p11181_0 := h11181c.1
                                        have p11181_1 := h11181c.2.1
                                        have p11181_2 := h11181c.2.2.1
                                        have p11181_3 := h11181c.2.2.2
                                        linarith only [hlam, p11181_0]
                                  · linarith only [h0, h10577, h11085, h11145, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h1, h11075, h11083, h11087, h11144, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h10577, h11075, h11083, h11087, h11140, h11143, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h10577, h11075, h11087, h11142, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h10577, h11075, h11087, h11140, h11141, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h11075, h11080, h11087, h11140, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h10577, h11075, h11082, hlam]
              · linarith only [h1, h11075, h11081, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h11223 | h11223
              · rcases m.htr 0 4 5 (by decide) (by decide) with h11224 | h11224
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11225 | h11225
                  · linarith only [h0, h1, h11080, h11225, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11227 | h11227
                    · linarith only [h0, h11078, h11227, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11229 | h11229
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11230 | h11230
                        · linarith only [h0, h1, h11080, h11225, h11230, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h11229, h11230, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11233 | h11233
                        · linarith only [h0, h1, h11080, h11225, h11233, hc12, hc23, hlam, hphi]
                        · linarith only [h1, h11075, h11229, h11233, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h11075, h11080, h11224, hlam]
              · linarith only [h1, h11075, h11223, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h11238 | h11238
        · linarith only [h0, h1, h11238, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h11240 | h11240
          · linarith only [h0, h10577, h11240, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h11242 | h11242
            · rcases m.htr 0 3 5 (by decide) (by decide) with h11243 | h11243
              · rcases m.htr 0 4 5 (by decide) (by decide) with h11244 | h11244
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11245 | h11245
                  · linarith only [h0, h1, h11238, h11245, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11247 | h11247
                    · linarith only [h0, h11075, h11240, h11244, h11247, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11249 | h11249
                      · linarith only [h0, h11075, h11249, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11251 | h11251
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11252 | h11252
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11253 | h11253
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11254 | h11254
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h11255 | h11255
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h11256 | h11256
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11257 | h11257
                                    · rcases h1bigk with h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [hlam, p11258_0]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [h11075, h11245, h11251, h11253, hc12, hc23, hlam, hphi, p11258_1]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [h1, hlam, p11258_0]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [h10577, hlam, p11258_0]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [h11075, hlam, p11258_0]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [h0, hlam, p11258_0]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [hlam, p11258_0]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [h11245, hlam, p11258_0]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [h11247, hlam, p11258_0]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [h11249, hlam, p11258_0]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [h0, h11245, hc12, hc23, hlam, hphi, p11258_1]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        rcases p11258_3 (m.d 0 1) (by simp) with h11270 | h11270
                                        · linarith only [h1, h11270, hlam]
                                        · linarith only [h0, h11270, hlam]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [hlam, p11258_0]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [h0, h10577, h11245, hc12, hc23, hlam, hphi, p11258_1]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [h0, h11075, h11245, hc12, hc23, hlam, hphi, p11258_1]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [h0, h11247, hc12, hc24, hlam, hphi, p11258_1]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        rcases p11258_3 (m.d 0 1) (by simp) with h11277 | h11277
                                        · linarith only [h10577, h11277, hlam]
                                        · linarith only [h0, h11277, hlam]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [h11251, hlam, p11258_0]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [hlam, p11258_0]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [h0, h11075, h11245, h11251, hc12, hc23, hlam, hphi, p11258_1]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [h0, h11249, hc12, hc25, hlam, hphi, p11258_1]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        rcases p11258_3 (m.d 0 1) (by simp) with h11284 | h11284
                                        · linarith only [h11075, h11284, hlam]
                                        · linarith only [h0, h11284, hlam]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [h11252, hlam, p11258_0]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [h11253, hlam, p11258_0]
                                      · have p11258_0 := h11258c.1
                                        have p11258_1 := h11258c.2.1
                                        have p11258_2 := h11258c.2.2.1
                                        have p11258_3 := h11258c.2.2.2
                                        linarith only [hlam, p11258_0]
                                    · rcases h1bigk with h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c | h11290c
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [hlam, p11290_0]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [h1, h11245, hc12, hc23, hlam, hphi, p11290_1]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [h1, hlam, p11290_0]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [h10577, hlam, p11290_0]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [h11075, hlam, p11290_0]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [h0, hlam, p11290_0]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [hlam, p11290_0]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [h11245, hlam, p11290_0]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [h11247, hlam, p11290_0]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [h11249, hlam, p11290_0]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [h0, h11245, hc12, hc23, hlam, hphi, p11290_1]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        rcases p11290_3 (m.d 0 1) (by simp) with h11302 | h11302
                                        · linarith only [h1, h11302, hlam]
                                        · linarith only [h0, h11302, hlam]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [hlam, p11290_0]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [h0, h10577, h11245, hc12, hc23, hlam, hphi, p11290_1]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [h0, h11075, h11245, hc12, hc23, hlam, hphi, p11290_1]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [h0, h11247, h11254, hc12, hc23, hlam, hphi, p11290_1]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        rcases p11290_3 (m.d 0 1) (by simp) with h11309 | h11309
                                        · linarith only [h10577, h11309, hlam]
                                        · linarith only [h0, h11309, hlam]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [h11251, hlam, p11290_0]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [hlam, p11290_0]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [h0, h11075, h11247, h11254, hc12, hc23, hlam, hphi, p11290_1]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [h0, h11249, h11254, h11256, hc12, hc23, hlam, hphi, p11290_1]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        rcases p11290_3 (m.d 0 1) (by simp) with h11316 | h11316
                                        · linarith only [h11075, h11316, hlam]
                                        · linarith only [h0, h11316, hlam]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [h11252, hlam, p11290_0]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [h11253, hlam, p11290_0]
                                      · have p11290_0 := h11290c.1
                                        have p11290_1 := h11290c.2.1
                                        have p11290_2 := h11290c.2.2.1
                                        have p11290_3 := h11290c.2.2.2
                                        linarith only [hlam, p11290_0]
                                  · linarith only [h0, h10577, h11242, h11244, h11247, h11256, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · linarith only [h0, h1, h11245, h11255, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h11245, h11254, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h10577, h11244, h11253, hlam]
                          · linarith only [h1, h11243, h11252, hlam]
                        · linarith only [h1, h11242, h11251, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11328 | h11328
                  · linarith only [h0, h10577, h11244, h11328, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11330 | h11330
                    · linarith only [h0, h10577, h11244, h11330, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11332 | h11332
                      · linarith only [h0, h11075, h11332, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11334 | h11334
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11335 | h11335
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11336 | h11336
                            · linarith only [h0, h10577, h11244, h11328, h11334, h11336, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h10577, h11336, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h0, h1, h11243, h11335, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h0, h1, h11334, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h11341 | h11341
                · linarith only [h11242, h11243, h11341, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11343 | h11343
                  · linarith only [h0, h10577, h11341, h11343, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11345 | h11345
                    · linarith only [h0, h10577, h11341, h11345, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11347 | h11347
                      · linarith only [h0, h11075, h11347, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11349 | h11349
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11350 | h11350
                          · linarith only [h0, h10577, h11242, h11243, h11343, h11350, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h11350, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h11242, h11243, h11349, hc12, hc35, hlam, hphi, ht23]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h11354 | h11354
              · rcases m.htr 0 4 5 (by decide) (by decide) with h11355 | h11355
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11356 | h11356
                  · linarith only [h0, h1, h11242, h11356, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11358 | h11358
                    · linarith only [h0, h11075, h11240, h11242, h11354, h11358, hc02, hc34, hlam, hphi, ht23]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11360 | h11360
                      · linarith only [h0, h11075, h11360, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11362 | h11362
                        · linarith only [h0, h11075, h11242, h11354, h11356, h11362, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h11362, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h11242, h11354, h11355, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h11366 | h11366
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11367 | h11367
                  · linarith only [h0, h1, h11354, h11367, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11369 | h11369
                    · linarith only [h0, h1, h11240, h11354, h11369, hc02, hc35, hlam, hphi, ht23]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11371 | h11371
                      · linarith only [h0, h11075, h11371, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11373 | h11373
                        · linarith only [h0, h1, h11242, h11367, h11373, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h11373, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11376 | h11376
                  · linarith only [h0, h1, h11354, h11376, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11378 | h11378
                    · linarith only [h0, h1, h11242, h11366, h11378, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11380 | h11380
                      · linarith only [h0, h11075, h11380, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11382 | h11382
                        · linarith only [h0, h1, h11242, h11376, h11382, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h11382, hc12, hc34, hlam, hphi, ht23]

end R2N4
