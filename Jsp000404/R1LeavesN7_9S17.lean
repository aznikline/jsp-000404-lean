import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_9S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8270000 in
set_option maxHeartbeats 8270000 in
theorem r1l7_13_24_L_I_H_I_s11_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11548 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11549 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  have h10295 := hg10295
  rcases m.htr 0 3 4 (by decide) (by decide) with h13560 | h13560
  · linarith only [h11548, h11549, h13560, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h13562 | h13562
    · rcases m.htr 0 4 5 (by decide) (by decide) with h13563 | h13563
      · rcases m.htr 1 2 3 (by decide) (by decide) with h13564 | h13564
        · rcases m.htr 1 2 4 (by decide) (by decide) with h13565 | h13565
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13566 | h13566
            · rcases m.htr 1 3 5 (by decide) (by decide) with h13567 | h13567
              · rcases m.htr 1 4 5 (by decide) (by decide) with h13568 | h13568
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13569 | h13569
                  · linarith only [h10295, h11548, h11549, h13560, h13562, h13565, h13569, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13571 | h13571
                    · linarith only [h11548, h11549, h13564, h13566, h13569, h13571, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h11548, h11549, h13562, h13564, h13566, h13569, h13571, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h13563, h13568, h8811, hlam]
              · linarith only [h13560, h13562, h13566, h13567, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h13576 | h13576
              · rcases m.htr 1 4 5 (by decide) (by decide) with h13577 | h13577
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13578 | h13578
                  · linarith only [h0, h11548, h13566, h13578, h8811, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13580 | h13580
                    · linarith only [h11548, h11549, h13565, h13580, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h11548, h11549, h13562, h13565, h13580, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h11548, h11549, h13562, h13563, h13565, h13577, hlam]
              · linarith only [h11548, h11549, h13562, h13565, h13576, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13585 | h13585
            · linarith only [h13560, h13562, h13564, h13565, h13585, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h13587 | h13587
              · rcases m.htr 1 4 5 (by decide) (by decide) with h13588 | h13588
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13589 | h13589
                  · linarith only [h0, h11548, h13565, h13585, h13589, h8811, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13591 | h13591
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h13592 | h13592
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13593 | h13593
                        · rcases h3bigk with h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c | h13594c
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [hlam, p13594_0]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [h7360, hlam, p13594_1]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [h0, h11548, h13565, h13589, hc23, hc34, hlam, hphi, p13594_1]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [h13560, hlam, p13594_0]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            rcases p13594_3 (m.d 0 3) (by simp) with h13599 | h13599
                            · rcases p13594_3 (m.d 1 3) (by simp) with h13600 | h13600
                              · rcases p13594_3 (m.d 2 3) (by simp) with h13601 | h13601
                                · linarith only [h11548, h13601, hlam]
                                · linarith only [h13591, h13601, hlam]
                              · linarith only [h13587, h13600, hlam]
                            · linarith only [h13599, hlam, p13594_0]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [h13564, h13565, h13589, hc03, hc34, hlam, hphi, p13594_1]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [hlam, p13594_0]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [h13564, h13565, h13589, h13591, h13593, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13594_1]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [h13585, hlam, p13594_0]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            rcases p13594_3 (m.d 0 3) (by simp) with h13610 | h13610
                            · linarith only [h13610, h7360, hlam]
                            · linarith only [h13562, h13610, hlam]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [h11548, hlam, p13594_0]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [h13564, hlam, p13594_0]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [hlam, p13594_0]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [h13589, hlam, p13594_0]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [h0, h11548, h13565, h13589, h13593, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13594_1]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            rcases p13594_3 (m.d 0 3) (by simp) with h13618 | h13618
                            · linarith only [h13618, hlam, p13594_0]
                            · rcases p13594_3 (m.d 1 3) (by simp) with h13620 | h13620
                              · linarith only [h13585, h13620, hlam]
                              · linarith only [h13620, h7360, hlam]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [h7360, hc01, hc34, hlam, hphi, ht12, ht23, p13594_1]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            rcases p13594_3 (m.d 0 3) (by simp) with h13624 | h13624
                            · linarith only [h13560, h13624, hlam]
                            · linarith only [h11548, h13624, hlam]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [hlam, p13594_0]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [h0, h11548, h13565, h13589, h13591, hlam, p13594_2]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [h13562, hlam, p13594_0]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [h13587, hlam, p13594_0]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [h13591, hlam, p13594_0]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [h13593, hlam, p13594_0]
                          · have p13594_0 := h13594c.1
                            have p13594_1 := h13594c.2.1
                            have p13594_2 := h13594c.2.2.1
                            have p13594_3 := h13594c.2.2.2
                            linarith only [hlam, p13594_0]
                        · linarith only [h0, h11548, h13565, h13589, h13593, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h11548, h13563, h13565, h13591, h13592, hc04, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h11548, h13562, h13565, h13589, h13591, hc23, hc34, hlam, hphi]
                · linarith only [h10295, h13563, h13564, h13565, h13587, h13588, h8811, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h11548, h13562, h13565, h13587, h7360, hc01, hc24, hlam, hphi, ht12]
        · linarith only [h0, h11548, h13564, hlam]
      · linarith only [h11548, h11549, h13562, h13563, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h13641 | h13641
      · rcases m.htr 1 2 3 (by decide) (by decide) with h13642 | h13642
        · rcases m.htr 1 2 4 (by decide) (by decide) with h13643 | h13643
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13644 | h13644
            · rcases m.htr 1 3 5 (by decide) (by decide) with h13645 | h13645
              · rcases m.htr 1 4 5 (by decide) (by decide) with h13646 | h13646
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13647 | h13647
                  · linarith only [h0, h11548, h13560, h13647, h7360, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13649 | h13649
                    · linarith only [h11548, h11549, h13562, h13649, h7360, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h13651 | h13651
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13652 | h13652
                        · rcases h3bigk with h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c | h13653c
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [hlam, p13653_0]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [h7360, hlam, p13653_1]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [h13562, hc23, hc35, hlam, hphi, p13653_1]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [h13560, hlam, p13653_0]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [h13562, hlam, p13653_0]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            rcases p13653_3 (m.d 0 3) (by simp) with h13659 | h13659
                            · linarith only [h13659, h7360, hlam]
                            · rcases p13653_3 (m.d 1 3) (by simp) with h13661 | h13661
                              · rcases p13653_3 (m.d 2 3) (by simp) with h13662 | h13662
                                · linarith only [h13642, h13662, hlam]
                                · rcases p13653_3 (m.d 3 4) (by simp) with h13664 | h13664
                                  · linarith only [h13644, h13664, hlam]
                                  · linarith only [h13560, h13664, hlam]
                              · linarith only [h13661, h7360, hlam]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [hlam, p13653_0]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [h11548, h11549, h13644, h13647, hlam, p13653_2]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [h11548, h11549, h13642, h13647, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13653_1]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [h13562, h13642, h7360, hc01, hc12, hlam, hphi, p13653_1]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [h11548, hlam, p13653_0]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [h13642, hlam, p13653_0]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [hlam, p13653_0]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [h13647, hlam, p13653_0]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [h13649, hlam, p13653_0]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [h13642, h13644, h7360, hc01, hc12, hlam, hphi, p13653_1]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [h13644, hlam, p13653_0]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            rcases p13653_3 (m.d 0 3) (by simp) with h13679 | h13679
                            · linarith only [h13560, h13679, hlam]
                            · linarith only [h11548, h13679, hlam]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [hlam, p13653_0]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [h13562, h13642, h13644, h7360, hc01, hc12, hlam, hphi, p13653_1]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [h13642, h13645, h7360, hc01, hc12, hlam, hphi, p13653_1]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [h13645, hlam, p13653_0]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            rcases p13653_3 (m.d 0 3) (by simp) with h13686 | h13686
                            · linarith only [h13562, h13686, hlam]
                            · linarith only [h11548, h13686, hlam]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [h13652, hlam, p13653_0]
                          · have p13653_0 := h13653c.1
                            have p13653_1 := h13653c.2.1
                            have p13653_2 := h13653c.2.2.1
                            have p13653_3 := h13653c.2.2.2
                            linarith only [hlam, p13653_0]
                        · linarith only [h13560, h13641, h13652, hlam]
                      · linarith only [h11549, h13641, h13651, hlam]
                · linarith only [h11549, h13641, h13646, h8811, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h11548, h11549, h13560, h13644, h13645, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h13695 | h13695
              · linarith only [h13562, h13644, h13695, h7360, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h13697 | h13697
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13698 | h13698
                  · linarith only [h11548, h13644, h13698, h7360, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13700 | h13700
                    · linarith only [h11548, h11549, h13643, h13700, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h13702 | h13702
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13703 | h13703
                        · rcases h3bigk with h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c | h13704c
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [hlam, p13704_0]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [h7360, hlam, p13704_1]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [h13695, h7360, hc23, hc35, hlam, hphi, p13704_1]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [h13560, hlam, p13704_0]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [h13562, hlam, p13704_0]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [h13695, hc03, hc35, hlam, hphi, p13704_1]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [hlam, p13704_0]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [h13695, hc23, hc35, hlam, hphi, p13704_1]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [h13644, hlam, p13704_0]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [h13695, hlam, p13704_0]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [h11548, hlam, p13704_0]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [h13642, hlam, p13704_0]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [hlam, p13704_0]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [h13698, hlam, p13704_0]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [h13700, hlam, p13704_0]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            rcases p13704_3 (m.d 0 3) (by simp) with h13720 | h13720
                            · linarith only [h13720, hlam, p13704_0]
                            · rcases p13704_3 (m.d 1 3) (by simp) with h13722 | h13722
                              · linarith only [h13644, h13722, hlam]
                              · linarith only [h13722, h7360, hlam]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [h7360, hc01, hc34, hlam, hphi, ht12, ht23, p13704_1]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            rcases p13704_3 (m.d 0 3) (by simp) with h13726 | h13726
                            · linarith only [h13560, h13726, hlam]
                            · linarith only [h11548, h13726, hlam]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [hlam, p13704_0]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [h13562, h7360, hc01, hc34, hlam, hphi, ht12, ht23, p13704_1]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            rcases p13704_3 (m.d 0 3) (by simp) with h13731 | h13731
                            · linarith only [h13731, hlam, p13704_0]
                            · rcases p13704_3 (m.d 1 3) (by simp) with h13733 | h13733
                              · linarith only [h13695, h13733, hlam]
                              · linarith only [h13733, h7360, hlam]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [h7360, hc01, hc35, hlam, hphi, ht12, ht23, p13704_1]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            rcases p13704_3 (m.d 0 3) (by simp) with h13737 | h13737
                            · linarith only [h13562, h13737, hlam]
                            · linarith only [h11548, h13737, hlam]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [h13703, hlam, p13704_0]
                          · have p13704_0 := h13704c.1
                            have p13704_1 := h13704c.2.1
                            have p13704_2 := h13704c.2.2.1
                            have p13704_3 := h13704c.2.2.2
                            linarith only [hlam, p13704_0]
                        · linarith only [h11549, h13641, h13643, h13644, h13703, h8811, hc01, hc12, hlam, hphi]
                      · linarith only [h11549, h13641, h13702, hlam]
                · linarith only [h11549, h13641, h13643, h13697, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13745 | h13745
            · linarith only [h13560, h13642, h13643, h13745, h7360, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h13747 | h13747
              · linarith only [h13562, h13642, h13643, h13747, h7360, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h13749 | h13749
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13750 | h13750
                  · linarith only [h11548, h13642, h13643, h13745, h13750, h7360, h8811, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13752 | h13752
                    · linarith only [h11548, h13747, h13752, h7360, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h13754 | h13754
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13755 | h13755
                        · rcases h3bigk with h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c | h13756c
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [hlam, p13756_0]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [h7360, hlam, p13756_1]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [h13642, h13643, h13750, h7360, hc23, hc34, hlam, hphi, p13756_1]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [h13560, hlam, p13756_0]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [h13562, hlam, p13756_0]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [h13642, h13643, h13750, hc03, hc34, hlam, hphi, p13756_1]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [hlam, p13756_0]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [h13642, h13643, h13750, hc23, hc34, hlam, hphi, p13756_1]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [h13745, hlam, p13756_0]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [h13747, hlam, p13756_0]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [h11548, hlam, p13756_0]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [h13642, hlam, p13756_0]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [hlam, p13756_0]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [h13750, hlam, p13756_0]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [h13752, hlam, p13756_0]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            rcases p13756_3 (m.d 0 3) (by simp) with h13772 | h13772
                            · linarith only [h13772, hlam, p13756_0]
                            · rcases p13756_3 (m.d 1 3) (by simp) with h13774 | h13774
                              · linarith only [h13745, h13774, hlam]
                              · linarith only [h13774, h7360, hlam]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [h7360, hc01, hc34, hlam, hphi, ht12, ht23, p13756_1]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            rcases p13756_3 (m.d 0 3) (by simp) with h13778 | h13778
                            · linarith only [h13560, h13778, hlam]
                            · linarith only [h11548, h13778, hlam]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [hlam, p13756_0]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [h13747, h7360, hc01, hc34, hlam, hphi, ht12, ht23, p13756_1]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            rcases p13756_3 (m.d 0 3) (by simp) with h13783 | h13783
                            · linarith only [h13783, hlam, p13756_0]
                            · rcases p13756_3 (m.d 1 3) (by simp) with h13785 | h13785
                              · linarith only [h13747, h13785, hlam]
                              · linarith only [h13785, h7360, hlam]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [h7360, hc01, hc35, hlam, hphi, ht12, ht23, p13756_1]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            rcases p13756_3 (m.d 0 3) (by simp) with h13789 | h13789
                            · linarith only [h13562, h13789, hlam]
                            · linarith only [h11548, h13789, hlam]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [h13755, hlam, p13756_0]
                          · have p13756_0 := h13756c.1
                            have p13756_1 := h13756c.2.1
                            have p13756_2 := h13756c.2.2.1
                            have p13756_3 := h13756c.2.2.2
                            linarith only [hlam, p13756_0]
                        · linarith only [h0, h13643, h13750, h13755, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h13641, h13643, h13754, h8811, hlam]
                · linarith only [h13641, h13749, h8811, hlam]
        · linarith only [h0, h11548, h13642, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h13798 | h13798
        · rcases m.htr 1 2 4 (by decide) (by decide) with h13799 | h13799
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13800 | h13800
            · rcases m.htr 1 3 5 (by decide) (by decide) with h13801 | h13801
              · rcases m.htr 1 4 5 (by decide) (by decide) with h13802 | h13802
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13803 | h13803
                  · linarith only [h11548, h11549, h13560, h13803, h7360, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13805 | h13805
                    · linarith only [h11548, h11549, h13562, h13641, h13798, h13800, h13802, h13805, h7360, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h13807 | h13807
                      · linarith only [h11548, h11549, h13641, h13803, h13807, hc23, hc34, hlam, hphi]
                      · linarith only [h11548, h11549, h13798, h13800, h13802, h13807, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h11548, h11549, h13799, h13802, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h13560, h13800, h13801, h7360, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h13812 | h13812
              · linarith only [h13562, h13800, h13812, h7360, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h13814 | h13814
                · linarith only [h11548, h11549, h13641, h13800, h13814, hc23, hc34, hlam, hphi]
                · linarith only [h11548, h11549, h13799, h13814, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13817 | h13817
            · linarith only [h13560, h13798, h13799, h13817, h7360, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h13819 | h13819
              · linarith only [h13562, h13817, h13819, h7360, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h13821 | h13821
                · linarith only [h11548, h11549, h13641, h13817, h13821, hc23, hc34, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13823 | h13823
                  · linarith only [h0, h11548, h13799, h13821, h13823, hc34, hc45, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13825 | h13825
                    · linarith only [h0, h11548, h13799, h13819, h13821, h13825, h7360, hc03, hc45, hlam, hphi, ht34]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h13827 | h13827
                      · linarith only [h0, h13799, h13821, h13823, h13827, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h11548, h11549, h13827, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h11548, h11549, h13798, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 8270000 in
set_option maxHeartbeats 8270000 in
theorem r1l7_13_24_L_I_H_I_s11_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11548 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  have h10295 := hg10295
  rcases m.htr 0 2 4 (by decide) (by decide) with h11549 | h11549
  · exact r1l7_13_24_L_I_H_I_s11_x0_x0 m hb3 hb4 hg0 hg7360 hg8811 hg10295 h11548 h11549
  · exact r1l7_13_24_L_I_H_I_s11_x0_x1 m hb3 hb4 hg0 hg7360 hg8811 hg10295 h11548 h11549

end R2N4
