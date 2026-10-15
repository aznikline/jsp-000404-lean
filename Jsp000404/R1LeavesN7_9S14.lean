import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8270000 in
set_option maxHeartbeats 8270000 in
theorem r1l7_13_24_L_I_H_I_s11_x0_x0_x0_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11548 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11549 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11550 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11551 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11552 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h11553 | h11553
  · rcases m.htr 1 2 4 (by decide) (by decide) with h11554 | h11554
    · rcases m.htr 1 3 4 (by decide) (by decide) with h11555 | h11555
      · rcases m.htr 1 3 5 (by decide) (by decide) with h11556 | h11556
        · rcases m.htr 1 4 5 (by decide) (by decide) with h11557 | h11557
          · rcases m.htr 2 3 4 (by decide) (by decide) with h11558 | h11558
            · rcases m.htr 2 3 5 (by decide) (by decide) with h11559 | h11559
              · rcases m.htr 2 4 5 (by decide) (by decide) with h11560 | h11560
                · rcases m.htr 3 4 5 (by decide) (by decide) with h11561 | h11561
                  · rcases h3bigk with h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c | h11562c
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [hlam, p11562_0]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [h7360, hlam, p11562_1]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [h11548, h11558, h11561, hc02, hc45, hlam, hphi, ht0b, ht5b, p11562_1]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      rcases p11562_3 (m.d 0 3) (by simp) with h11566 | h11566
                      · rcases p11562_3 (m.d 1 3) (by simp) with h11567 | h11567
                        · rcases p11562_3 (m.d 2 3) (by simp) with h11568 | h11568
                          · linarith only [h11548, h11568, hlam]
                          · linarith only [h11558, h11568, hlam]
                        · linarith only [h11555, h11567, hlam]
                      · linarith only [h11566, hlam, p11562_0]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      rcases p11562_3 (m.d 0 3) (by simp) with h11573 | h11573
                      · rcases p11562_3 (m.d 1 3) (by simp) with h11574 | h11574
                        · rcases p11562_3 (m.d 2 3) (by simp) with h11575 | h11575
                          · linarith only [h11548, h11575, hlam]
                          · linarith only [h11559, h11575, hlam]
                        · linarith only [h11556, h11574, hlam]
                      · linarith only [h11573, hlam, p11562_0]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [h11548, h11553, h11558, h11561, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11562_1]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [hlam, p11562_0]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [h11553, h11558, h11561, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11562_1]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      rcases p11562_3 (m.d 0 3) (by simp) with h11583 | h11583
                      · linarith only [h11583, h7360, hlam]
                      · linarith only [h11550, h11583, hlam]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      rcases p11562_3 (m.d 0 3) (by simp) with h11586 | h11586
                      · linarith only [h11586, h7360, hlam]
                      · linarith only [h11551, h11586, hlam]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [h11548, hlam, p11562_0]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [h11553, hlam, p11562_0]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [hlam, p11562_0]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [h0, h11548, h11561, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11562_1]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      rcases p11562_3 (m.d 0 3) (by simp) with h11593 | h11593
                      · rcases p11562_3 (m.d 1 3) (by simp) with h11594 | h11594
                        · rcases p11562_3 (m.d 2 3) (by simp) with h11595 | h11595
                          · rcases p11562_3 (m.d 3 4) (by simp) with h11596 | h11596
                            · linarith only [h11558, h11596, hlam]
                            · linarith only [h11561, h11596, hlam]
                          · linarith only [h11595, hlam, p11562_0]
                        · linarith only [h11556, h11594, hlam]
                      · linarith only [h11551, h11593, hlam]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [h11550, hlam, p11562_0]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [h11555, hlam, p11562_0]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [h11558, hlam, p11562_0]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [hlam, p11562_0]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [h0, h11548, h11558, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p11562_1]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [h11551, hlam, p11562_0]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [h11556, hlam, p11562_0]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [h11559, hlam, p11562_0]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [h11561, hlam, p11562_0]
                    · have p11562_0 := h11562c.1
                      have p11562_1 := h11562c.2.1
                      have p11562_2 := h11562c.2.2.1
                      have p11562_3 := h11562c.2.2.2
                      linarith only [hlam, p11562_0]
                  · rcases h3bigk with h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [hlam, p11612_0]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [h7360, hlam, p11612_1]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [h11553, h11558, h11560, h11561, h7360, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11612_1]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      rcases p11612_3 (m.d 0 3) (by simp) with h11616 | h11616
                      · rcases p11612_3 (m.d 1 3) (by simp) with h11617 | h11617
                        · rcases p11612_3 (m.d 2 3) (by simp) with h11618 | h11618
                          · linarith only [h11548, h11618, hlam]
                          · linarith only [h11558, h11618, hlam]
                        · linarith only [h11555, h11617, hlam]
                      · linarith only [h11616, hlam, p11612_0]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      rcases p11612_3 (m.d 0 3) (by simp) with h11623 | h11623
                      · rcases p11612_3 (m.d 1 3) (by simp) with h11624 | h11624
                        · rcases p11612_3 (m.d 2 3) (by simp) with h11625 | h11625
                          · linarith only [h11548, h11625, hlam]
                          · linarith only [h11559, h11625, hlam]
                        · linarith only [h11556, h11624, hlam]
                      · linarith only [h11623, hlam, p11612_0]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [h11548, h11558, h11560, h11561, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11612_1]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [hlam, p11612_0]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [h11553, h11558, h11560, h11561, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11612_1]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      rcases p11612_3 (m.d 0 3) (by simp) with h11633 | h11633
                      · linarith only [h11633, h7360, hlam]
                      · linarith only [h11550, h11633, hlam]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      rcases p11612_3 (m.d 0 3) (by simp) with h11636 | h11636
                      · linarith only [h11636, h7360, hlam]
                      · linarith only [h11551, h11636, hlam]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [h11548, hlam, p11612_0]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [h11553, hlam, p11612_0]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [hlam, p11612_0]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      rcases p11612_3 (m.d 0 3) (by simp) with h11642 | h11642
                      · rcases p11612_3 (m.d 1 3) (by simp) with h11643 | h11643
                        · rcases p11612_3 (m.d 2 3) (by simp) with h11644 | h11644
                          · rcases p11612_3 (m.d 3 4) (by simp) with h11645 | h11645
                            · linarith only [h11645, hlam, p11612_0]
                            · rcases p11612_3 (m.d 3 5) (by simp) with h11647 | h11647
                              · linarith only [h11559, h11647, hlam]
                              · linarith only [h11561, h11647, hlam]
                          · linarith only [h11644, hlam, p11612_0]
                        · linarith only [h11555, h11643, hlam]
                      · linarith only [h11550, h11642, hlam]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      rcases p11612_3 (m.d 0 3) (by simp) with h11653 | h11653
                      · rcases p11612_3 (m.d 1 3) (by simp) with h11654 | h11654
                        · rcases p11612_3 (m.d 2 3) (by simp) with h11655 | h11655
                          · rcases p11612_3 (m.d 3 4) (by simp) with h11656 | h11656
                            · linarith only [h11558, h11656, hlam]
                            · rcases p11612_3 (m.d 3 5) (by simp) with h11658 | h11658
                              · linarith only [h11658, hlam, p11612_0]
                              · rcases h4bigk with h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c | h11660c
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [hlam, p11660_0]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [h8811, hlam, p11660_0]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [h11550, h11560, h11561, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p11660_1]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  rcases p11660_3 (m.d 0 4) (by simp) with h11664 | h11664
                                  · rcases p11660_3 (m.d 1 4) (by simp) with h11665 | h11665
                                    · rcases p11660_3 (m.d 2 4) (by simp) with h11666 | h11666
                                      · linarith only [h11549, h11666, hlam]
                                      · linarith only [h11558, h11666, hlam]
                                    · linarith only [h11555, h11665, hlam]
                                  · linarith only [h11550, h11664, hlam]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [h11548, h11550, h11561, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p11660_1]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [h11555, h8811, hc01, hc13, hlam, hphi, p11660_1]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [hlam, p11660_0]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [h11553, h11555, h11560, h11561, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11660_1]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  rcases p11660_3 (m.d 0 4) (by simp) with h11675 | h11675
                                  · linarith only [h11675, h8811, hlam]
                                  · linarith only [h11550, h11675, hlam]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [h11553, h11555, h11561, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11660_1]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [h11549, hlam, p11660_1]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [h11554, hlam, p11660_1]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [hlam, p11660_0]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [h0, h11548, h11558, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11660_1]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [h0, h11548, h11558, h11561, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11660_1]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [h11550, hlam, p11660_1]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [h11555, hlam, p11660_0]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [h11558, hlam, p11660_0]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [hlam, p11660_0]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [h11561, hlam, p11660_0]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [h11552, hlam, p11660_0]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [h11557, hlam, p11660_0]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [h11560, hlam, p11660_0]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p11660_1]
                                · have p11660_0 := h11660c.1
                                  have p11660_1 := h11660c.2.1
                                  have p11660_2 := h11660c.2.2.1
                                  have p11660_3 := h11660c.2.2.2
                                  linarith only [hlam, p11660_0]
                          · linarith only [h11655, hlam, p11612_0]
                        · linarith only [h11556, h11654, hlam]
                      · linarith only [h11551, h11653, hlam]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [h11550, hlam, p11612_0]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [h11555, hlam, p11612_0]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [h11558, hlam, p11612_0]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [hlam, p11612_0]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [h11561, hlam, p11612_1]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [h11551, hlam, p11612_0]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [h11556, hlam, p11612_0]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [h11559, hlam, p11612_0]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [h0, h11548, h11559, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11612_1]
                    · have p11612_0 := h11612c.1
                      have p11612_1 := h11612c.2.1
                      have p11612_2 := h11612c.2.2.1
                      have p11612_3 := h11612c.2.2.2
                      linarith only [hlam, p11612_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h11707 | h11707
                  · linarith only [h0, h11548, h11558, h11560, h11707, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases h3bigk with h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c | h11709c
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      linarith only [hlam, p11709_0]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      linarith only [h7360, hlam, p11709_1]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      rcases p11709_3 (m.d 0 3) (by simp) with h11712 | h11712
                      · rcases p11709_3 (m.d 1 3) (by simp) with h11713 | h11713
                        · rcases p11709_3 (m.d 2 3) (by simp) with h11714 | h11714
                          · linarith only [h11548, h11714, hlam]
                          · rcases p11709_3 (m.d 3 4) (by simp) with h11716 | h11716
                            · linarith only [h11550, h11716, hlam]
                            · rcases p11709_3 (m.d 3 5) (by simp) with h11718 | h11718
                              · linarith only [h11551, h11718, hlam]
                              · rcases h4bigk with h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c | h11720c
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [hlam, p11720_0]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [h8811, hlam, p11720_0]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  rcases p11720_3 (m.d 0 4) (by simp) with h11723 | h11723
                                  · rcases p11720_3 (m.d 1 4) (by simp) with h11724 | h11724
                                    · rcases p11720_3 (m.d 2 4) (by simp) with h11725 | h11725
                                      · linarith only [h11549, h11725, hlam]
                                      · rcases p11720_3 (m.d 3 4) (by simp) with h11727 | h11727
                                        · linarith only [h11550, h11727, hlam]
                                        · rcases p11720_3 (m.d 4 5) (by simp) with h11729 | h11729
                                          · linarith only [h11552, h11729, hlam]
                                          · linarith only [h11560, h11729, hlam]
                                    · linarith only [h11554, h11724, hlam]
                                  · linarith only [h11549, h11723, hlam]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  rcases p11720_3 (m.d 0 4) (by simp) with h11734 | h11734
                                  · rcases p11720_3 (m.d 1 4) (by simp) with h11735 | h11735
                                    · rcases p11720_3 (m.d 2 4) (by simp) with h11736 | h11736
                                      · linarith only [h11549, h11736, hlam]
                                      · linarith only [h11558, h11736, hlam]
                                    · linarith only [h11555, h11735, hlam]
                                  · linarith only [h11550, h11734, hlam]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [h11553, h11555, h11558, h11560, h8811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11720_1]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [h11553, h11555, h8811, hc01, hc12, hlam, hphi, p11720_1]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [hlam, p11720_0]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  rcases p11720_3 (m.d 0 4) (by simp) with h11744 | h11744
                                  · linarith only [h11744, h8811, hlam]
                                  · linarith only [h11549, h11744, hlam]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  rcases p11720_3 (m.d 0 4) (by simp) with h11747 | h11747
                                  · linarith only [h11747, h8811, hlam]
                                  · linarith only [h11550, h11747, hlam]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [h11553, h11555, h11558, h11560, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11720_1]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [h11549, hlam, p11720_1]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [h11554, hlam, p11720_1]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [hlam, p11720_0]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [h11552, h11560, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p11720_1]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [h11560, hlam, p11720_0]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [h11550, hlam, p11720_1]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [h11555, hlam, p11720_0]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [h11558, hlam, p11720_0]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [hlam, p11720_0]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [h11707, hlam, p11720_0]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [h11552, hlam, p11720_0]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [h11557, hlam, p11720_0]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [h11552, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p11720_1]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [h11552, h11553, h11555, h8811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11720_1]
                                · have p11720_0 := h11720c.1
                                  have p11720_1 := h11720c.2.1
                                  have p11720_2 := h11720c.2.2.1
                                  have p11720_3 := h11720c.2.2.2
                                  linarith only [hlam, p11720_0]
                        · linarith only [h11553, h11713, hlam]
                      · linarith only [h11548, h11712, hlam]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      rcases p11709_3 (m.d 0 3) (by simp) with h11768 | h11768
                      · rcases p11709_3 (m.d 1 3) (by simp) with h11769 | h11769
                        · rcases p11709_3 (m.d 2 3) (by simp) with h11770 | h11770
                          · linarith only [h11548, h11770, hlam]
                          · linarith only [h11558, h11770, hlam]
                        · linarith only [h11555, h11769, hlam]
                      · linarith only [h11768, hlam, p11709_0]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      rcases p11709_3 (m.d 0 3) (by simp) with h11775 | h11775
                      · rcases p11709_3 (m.d 1 3) (by simp) with h11776 | h11776
                        · rcases p11709_3 (m.d 2 3) (by simp) with h11777 | h11777
                          · linarith only [h11548, h11777, hlam]
                          · linarith only [h11559, h11777, hlam]
                        · linarith only [h11556, h11776, hlam]
                      · linarith only [h11775, hlam, p11709_0]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      linarith only [h11550, h11552, h11553, h11558, h11560, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11709_1]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      linarith only [hlam, p11709_0]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      rcases p11709_3 (m.d 0 3) (by simp) with h11784 | h11784
                      · linarith only [h11784, h7360, hlam]
                      · linarith only [h11548, h11784, hlam]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      rcases p11709_3 (m.d 0 3) (by simp) with h11787 | h11787
                      · linarith only [h11787, h7360, hlam]
                      · linarith only [h11550, h11787, hlam]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      rcases p11709_3 (m.d 0 3) (by simp) with h11790 | h11790
                      · linarith only [h11790, h7360, hlam]
                      · linarith only [h11551, h11790, hlam]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      linarith only [h11548, hlam, p11709_0]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      linarith only [h11553, hlam, p11709_0]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      linarith only [hlam, p11709_0]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      rcases p11709_3 (m.d 0 3) (by simp) with h11796 | h11796
                      · rcases p11709_3 (m.d 1 3) (by simp) with h11797 | h11797
                        · rcases p11709_3 (m.d 2 3) (by simp) with h11798 | h11798
                          · rcases p11709_3 (m.d 3 4) (by simp) with h11799 | h11799
                            · linarith only [h11799, hlam, p11709_0]
                            · rcases p11709_3 (m.d 3 5) (by simp) with h11801 | h11801
                              · linarith only [h11559, h11801, hlam]
                              · linarith only [h11707, h11801, hlam]
                          · linarith only [h11798, hlam, p11709_0]
                        · linarith only [h11555, h11797, hlam]
                      · linarith only [h11550, h11796, hlam]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      rcases p11709_3 (m.d 0 3) (by simp) with h11807 | h11807
                      · rcases p11709_3 (m.d 1 3) (by simp) with h11808 | h11808
                        · rcases p11709_3 (m.d 2 3) (by simp) with h11809 | h11809
                          · rcases p11709_3 (m.d 3 4) (by simp) with h11810 | h11810
                            · linarith only [h11558, h11810, hlam]
                            · rcases p11709_3 (m.d 3 5) (by simp) with h11812 | h11812
                              · linarith only [h11812, hlam, p11709_0]
                              · rcases h4bigk with h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c | h11814c
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [hlam, p11814_0]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [h8811, hlam, p11814_0]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  rcases p11814_3 (m.d 0 4) (by simp) with h11817 | h11817
                                  · rcases p11814_3 (m.d 1 4) (by simp) with h11818 | h11818
                                    · rcases p11814_3 (m.d 2 4) (by simp) with h11819 | h11819
                                      · linarith only [h11549, h11819, hlam]
                                      · rcases p11814_3 (m.d 3 4) (by simp) with h11821 | h11821
                                        · linarith only [h11550, h11821, hlam]
                                        · rcases p11814_3 (m.d 4 5) (by simp) with h11823 | h11823
                                          · linarith only [h11552, h11823, hlam]
                                          · linarith only [h11560, h11823, hlam]
                                    · linarith only [h11554, h11818, hlam]
                                  · linarith only [h11549, h11817, hlam]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  rcases p11814_3 (m.d 0 4) (by simp) with h11828 | h11828
                                  · rcases p11814_3 (m.d 1 4) (by simp) with h11829 | h11829
                                    · rcases p11814_3 (m.d 2 4) (by simp) with h11830 | h11830
                                      · linarith only [h11549, h11830, hlam]
                                      · linarith only [h11558, h11830, hlam]
                                    · linarith only [h11555, h11829, hlam]
                                  · linarith only [h11550, h11828, hlam]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [h11550, h11558, h11560, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p11814_1]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [h11555, h8811, hc01, hc13, hlam, hphi, p11814_1]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [hlam, p11814_0]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  rcases p11814_3 (m.d 0 4) (by simp) with h11838 | h11838
                                  · linarith only [h11838, h8811, hlam]
                                  · linarith only [h11549, h11838, hlam]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  rcases p11814_3 (m.d 0 4) (by simp) with h11841 | h11841
                                  · linarith only [h11841, h8811, hlam]
                                  · linarith only [h11550, h11841, hlam]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [h11553, h11555, h11558, h11560, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11814_1]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [h11549, hlam, p11814_1]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [h11554, hlam, p11814_1]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [hlam, p11814_0]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [h11552, h11560, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p11814_1]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [h11560, hlam, p11814_0]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [h11550, hlam, p11814_1]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [h11555, hlam, p11814_0]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [h11558, hlam, p11814_0]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [hlam, p11814_0]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [h11707, hlam, p11814_0]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [h11552, hlam, p11814_0]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [h11557, hlam, p11814_0]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [h11552, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p11814_1]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [h11552, h11553, h11555, h8811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11814_1]
                                · have p11814_0 := h11814c.1
                                  have p11814_1 := h11814c.2.1
                                  have p11814_2 := h11814c.2.2.1
                                  have p11814_3 := h11814c.2.2.2
                                  linarith only [hlam, p11814_0]
                          · linarith only [h11809, hlam, p11709_0]
                        · linarith only [h11556, h11808, hlam]
                      · linarith only [h11551, h11807, hlam]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      linarith only [h11550, hlam, p11709_0]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      linarith only [h11555, hlam, p11709_0]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      linarith only [h11558, hlam, p11709_0]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      linarith only [hlam, p11709_0]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      linarith only [h11707, hlam, p11709_1]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      linarith only [h11551, hlam, p11709_0]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      linarith only [h11556, hlam, p11709_0]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      linarith only [h11559, hlam, p11709_0]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      linarith only [h0, h11548, h11559, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11709_1]
                    · have p11709_0 := h11709c.1
                      have p11709_1 := h11709c.2.1
                      have p11709_2 := h11709c.2.2.1
                      have p11709_3 := h11709c.2.2.2
                      linarith only [hlam, p11709_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h11873 | h11873
                · linarith only [h11558, h11559, h11873, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h11875 | h11875
                  · linarith only [h0, h11548, h11551, h11558, h11559, h11873, h11875, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases h3bigk with h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c | h11877c
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [hlam, p11877_0]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [h7360, hlam, p11877_1]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      rcases p11877_3 (m.d 0 3) (by simp) with h11880 | h11880
                      · rcases p11877_3 (m.d 1 3) (by simp) with h11881 | h11881
                        · rcases p11877_3 (m.d 2 3) (by simp) with h11882 | h11882
                          · linarith only [h11548, h11882, hlam]
                          · rcases p11877_3 (m.d 3 4) (by simp) with h11884 | h11884
                            · linarith only [h11550, h11884, hlam]
                            · rcases p11877_3 (m.d 3 5) (by simp) with h11886 | h11886
                              · linarith only [h11551, h11886, hlam]
                              · linarith only [h11559, h11886, hlam]
                        · linarith only [h11553, h11881, hlam]
                      · linarith only [h11548, h11880, hlam]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [h11550, h11552, h11558, h11559, h11875, hlam, p11877_2]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [h11558, h11559, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p11877_1]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [h11551, h11553, h11558, h11559, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11877_1]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [hlam, p11877_0]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      rcases p11877_3 (m.d 0 3) (by simp) with h11895 | h11895
                      · linarith only [h11895, h7360, hlam]
                      · linarith only [h11548, h11895, hlam]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [h11550, h11552, h11558, h11559, h11875, h7360, hlam, p11877_2]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [h11558, h11559, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11877_1]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [h11548, hlam, p11877_0]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [h11553, hlam, p11877_0]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [hlam, p11877_0]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [h11550, h11552, h11559, h11875, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p11877_1]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [h11559, hlam, p11877_0]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [h11550, hlam, p11877_0]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [h11555, hlam, p11877_0]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [h11558, hlam, p11877_0]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [hlam, p11877_0]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [h11875, hlam, p11877_1]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [h11551, hlam, p11877_0]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [h11556, hlam, p11877_0]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [h0, h11548, h11550, h11552, h11558, h11875, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11877_1]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      rcases p11877_3 (m.d 0 3) (by simp) with h11913 | h11913
                      · rcases p11877_3 (m.d 1 3) (by simp) with h11914 | h11914
                        · rcases p11877_3 (m.d 2 3) (by simp) with h11915 | h11915
                          · linarith only [h11559, h11915, hlam]
                          · linarith only [h11558, h11915, hlam]
                        · linarith only [h11555, h11914, hlam]
                      · linarith only [h11550, h11913, hlam]
                    · have p11877_0 := h11877c.1
                      have p11877_1 := h11877c.2.1
                      have p11877_2 := h11877c.2.2.1
                      have p11877_3 := h11877c.2.2.2
                      linarith only [hlam, p11877_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h11921 | h11921
              · rcases m.htr 2 4 5 (by decide) (by decide) with h11922 | h11922
                · rcases m.htr 3 4 5 (by decide) (by decide) with h11923 | h11923
                  · rcases h3bigk with h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c | h11924c
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [hlam, p11924_0]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [h7360, hlam, p11924_1]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      rcases p11924_3 (m.d 0 3) (by simp) with h11927 | h11927
                      · rcases p11924_3 (m.d 1 3) (by simp) with h11928 | h11928
                        · rcases p11924_3 (m.d 2 3) (by simp) with h11929 | h11929
                          · linarith only [h11548, h11929, hlam]
                          · rcases p11924_3 (m.d 3 4) (by simp) with h11931 | h11931
                            · linarith only [h11550, h11931, hlam]
                            · linarith only [h11558, h11931, hlam]
                        · linarith only [h11553, h11928, hlam]
                      · linarith only [h11548, h11927, hlam]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [h0, h11548, h11558, h11921, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p11924_1]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [h11550, h11558, h11921, hlam, p11924_2]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [h11550, h11553, h11558, h11921, h11923, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11924_1]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [hlam, p11924_0]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      rcases p11924_3 (m.d 0 3) (by simp) with h11940 | h11940
                      · linarith only [h11940, h7360, hlam]
                      · linarith only [h11548, h11940, hlam]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [h11553, h11558, h11921, h11923, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11924_1]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [h11550, h11558, h11921, h7360, hlam, p11924_2]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [h11548, hlam, p11924_0]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [h11553, hlam, p11924_0]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [hlam, p11924_0]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [h11558, hlam, p11924_0]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [h11550, h11558, h11923, hc03, hc45, hlam, hphi, ht0b, ht5b, p11924_1]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [h11550, hlam, p11924_0]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [h11555, hlam, p11924_0]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [h0, h11548, h11550, h11921, h11923, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11924_1]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [hlam, p11924_0]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      rcases p11924_3 (m.d 0 3) (by simp) with h11954 | h11954
                      · rcases p11924_3 (m.d 1 3) (by simp) with h11955 | h11955
                        · rcases p11924_3 (m.d 2 3) (by simp) with h11956 | h11956
                          · linarith only [h11558, h11956, hlam]
                          · linarith only [h11921, h11956, hlam]
                        · linarith only [h11556, h11955, hlam]
                      · linarith only [h11551, h11954, hlam]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [h11551, hlam, p11924_0]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [h11556, hlam, p11924_0]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [h11921, hlam, p11924_0]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [h11923, hlam, p11924_0]
                    · have p11924_0 := h11924c.1
                      have p11924_1 := h11924c.2.1
                      have p11924_2 := h11924c.2.2.1
                      have p11924_3 := h11924c.2.2.2
                      linarith only [hlam, p11924_0]
                  · linarith only [h0, h11548, h11550, h11552, h11558, h11921, h11923, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h11558, h11921, h11922, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h11968 | h11968
                · rcases m.htr 3 4 5 (by decide) (by decide) with h11969 | h11969
                  · rcases h3bigk with h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c | h11970c
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      linarith only [hlam, p11970_0]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      linarith only [h7360, hlam, p11970_1]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      rcases p11970_3 (m.d 0 3) (by simp) with h11973 | h11973
                      · rcases p11970_3 (m.d 1 3) (by simp) with h11974 | h11974
                        · rcases p11970_3 (m.d 2 3) (by simp) with h11975 | h11975
                          · linarith only [h11548, h11975, hlam]
                          · rcases p11970_3 (m.d 3 4) (by simp) with h11977 | h11977
                            · linarith only [h11550, h11977, hlam]
                            · linarith only [h11558, h11977, hlam]
                        · linarith only [h11553, h11974, hlam]
                      · linarith only [h11548, h11973, hlam]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      rcases p11970_3 (m.d 0 3) (by simp) with h11982 | h11982
                      · rcases p11970_3 (m.d 1 3) (by simp) with h11983 | h11983
                        · rcases p11970_3 (m.d 2 3) (by simp) with h11984 | h11984
                          · linarith only [h11548, h11984, hlam]
                          · rcases p11970_3 (m.d 3 4) (by simp) with h11986 | h11986
                            · linarith only [h11986, hlam, p11970_0]
                            · rcases p11970_3 (m.d 3 5) (by simp) with h11988 | h11988
                              · linarith only [h11551, h11988, hlam]
                              · rcases h4bigk with h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c | h11990c
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [hlam, p11990_0]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h8811, hlam, p11990_0]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h0, h11548, h11550, h11968, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11990_1]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h0, h11548, h11550, h11921, h11969, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11990_1]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  rcases p11990_3 (m.d 0 4) (by simp) with h11995 | h11995
                                  · rcases p11990_3 (m.d 1 4) (by simp) with h11996 | h11996
                                    · rcases p11990_3 (m.d 2 4) (by simp) with h11997 | h11997
                                      · linarith only [h11549, h11997, hlam]
                                      · linarith only [h11968, h11997, hlam]
                                    · linarith only [h11557, h11996, hlam]
                                  · linarith only [h11995, hlam, p11990_0]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h11553, h11555, h8811, hc01, hc12, hlam, hphi, p11990_1]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [hlam, p11990_0]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h11553, h11555, h11968, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11990_1]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h11553, h11555, h11921, h11969, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11990_1]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  rcases p11990_3 (m.d 0 4) (by simp) with h12006 | h12006
                                  · linarith only [h12006, h8811, hlam]
                                  · linarith only [h11552, h12006, hlam]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h11549, hlam, p11990_1]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h11554, hlam, p11990_1]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [hlam, p11990_0]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h11558, hlam, p11990_1]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h0, h11549, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11990_1]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h11550, hlam, p11990_1]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h11555, hlam, p11990_0]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h0, h11548, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11970_1, p11990_1]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [hlam, p11990_0]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h0, h11548, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11970_1, p11990_1]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h11552, hlam, p11990_0]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h11557, hlam, p11990_0]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h11968, hlam, p11990_0]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [h11969, hlam, p11990_0]
                                · have p11990_0 := h11990c.1
                                  have p11990_1 := h11990c.2.1
                                  have p11990_2 := h11990c.2.2.1
                                  have p11990_3 := h11990c.2.2.2
                                  linarith only [hlam, p11990_0]
                        · linarith only [h11555, h11983, hlam]
                      · linarith only [h11982, hlam, p11970_0]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      rcases p11970_3 (m.d 0 3) (by simp) with h12026 | h12026
                      · rcases p11970_3 (m.d 1 3) (by simp) with h12027 | h12027
                        · rcases p11970_3 (m.d 2 3) (by simp) with h12028 | h12028
                          · linarith only [h11548, h12028, hlam]
                          · rcases p11970_3 (m.d 3 4) (by simp) with h12030 | h12030
                            · linarith only [h11550, h12030, hlam]
                            · linarith only [h11969, h12030, hlam]
                        · linarith only [h11556, h12027, hlam]
                      · linarith only [h12026, hlam, p11970_0]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      linarith only [h11551, h11553, h11921, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11970_1]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      linarith only [hlam, p11970_0]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      rcases p11970_3 (m.d 0 3) (by simp) with h12037 | h12037
                      · linarith only [h12037, h7360, hlam]
                      · linarith only [h11548, h12037, hlam]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      rcases p11970_3 (m.d 0 3) (by simp) with h12040 | h12040
                      · linarith only [h12040, h7360, hlam]
                      · linarith only [h11550, h12040, hlam]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      rcases p11970_3 (m.d 0 3) (by simp) with h12043 | h12043
                      · linarith only [h12043, h7360, hlam]
                      · linarith only [h11551, h12043, hlam]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      linarith only [h11548, hlam, p11970_0]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      linarith only [h11553, hlam, p11970_0]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      linarith only [hlam, p11970_0]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      linarith only [h11558, hlam, p11970_0]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      linarith only [h11921, hlam, p11970_0]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      linarith only [h11550, hlam, p11970_0]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      linarith only [h11555, hlam, p11970_0]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      rcases p11970_3 (m.d 0 3) (by simp) with h12053 | h12053
                      · rcases p11970_3 (m.d 1 3) (by simp) with h12054 | h12054
                        · rcases p11970_3 (m.d 2 3) (by simp) with h12055 | h12055
                          · linarith only [h12055, hlam, p11970_0]
                          · rcases p11970_3 (m.d 3 4) (by simp) with h12057 | h12057
                            · rcases p11970_3 (m.d 3 5) (by simp) with h12058 | h12058
                              · linarith only [h11969, h12058, hlam]
                              · linarith only [h11921, h12058, hlam]
                            · linarith only [h12057, hlam, p11970_0]
                        · linarith only [h11553, h12054, hlam]
                      · linarith only [h11548, h12053, hlam]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      linarith only [hlam, p11970_0]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      linarith only [h11550, h11921, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11970_1]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      linarith only [h11551, hlam, p11970_0]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      linarith only [h11556, hlam, p11970_0]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      rcases p11970_3 (m.d 0 3) (by simp) with h12068 | h12068
                      · rcases p11970_3 (m.d 1 3) (by simp) with h12069 | h12069
                        · rcases p11970_3 (m.d 2 3) (by simp) with h12070 | h12070
                          · linarith only [h12070, hlam, p11970_0]
                          · rcases p11970_3 (m.d 3 4) (by simp) with h12072 | h12072
                            · rcases p11970_3 (m.d 3 5) (by simp) with h12073 | h12073
                              · rcases h4bigk with h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c | h12074c
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [hlam, p12074_0]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h8811, hlam, p12074_0]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h11968, hc04, hc45, hlam, hphi, ht0b, ht5b, p12074_1]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h11553, h11555, h11558, h8811, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12074_1]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  rcases p12074_3 (m.d 0 4) (by simp) with h12079 | h12079
                                  · rcases p12074_3 (m.d 1 4) (by simp) with h12080 | h12080
                                    · rcases p12074_3 (m.d 2 4) (by simp) with h12081 | h12081
                                      · linarith only [h11549, h12081, hlam]
                                      · linarith only [h11968, h12081, hlam]
                                    · linarith only [h11557, h12080, hlam]
                                  · linarith only [h12079, hlam, p12074_0]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h11553, h11555, h8811, hc01, hc12, hlam, hphi, p12074_1]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [hlam, p12074_0]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h11553, h11555, h11968, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12074_1]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h11553, h11555, h11969, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11970_1, p12074_1]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  rcases p12074_3 (m.d 0 4) (by simp) with h12090 | h12090
                                  · linarith only [h12090, h8811, hlam]
                                  · linarith only [h11552, h12090, hlam]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h11549, hlam, p12074_1]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h11554, hlam, p12074_1]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [hlam, p12074_0]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h11558, hlam, p12074_1]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h0, h11549, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12074_1]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h11550, hlam, p12074_1]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h11555, hlam, p12074_0]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h11550, h11553, h7360, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p12074_1]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [hlam, p12074_0]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h11550, h11553, h7360, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12074_1]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h11552, hlam, p12074_0]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h11557, hlam, p12074_0]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h11968, hlam, p12074_0]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [h11969, hlam, p12074_0]
                                · have p12074_0 := h12074c.1
                                  have p12074_1 := h12074c.2.1
                                  have p12074_2 := h12074c.2.2.1
                                  have p12074_3 := h12074c.2.2.2
                                  linarith only [hlam, p12074_0]
                              · linarith only [h12073, hlam, p11970_0]
                            · linarith only [h11558, h12072, hlam]
                        · linarith only [h11553, h12069, hlam]
                      · linarith only [h11548, h12068, hlam]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      linarith only [h11969, hlam, p11970_0]
                    · have p11970_0 := h11970c.1
                      have p11970_1 := h11970c.2.1
                      have p11970_2 := h11970c.2.2.1
                      have p11970_3 := h11970c.2.2.2
                      linarith only [hlam, p11970_0]
                  · linarith only [h0, h11549, h11558, h11968, h11969, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h12115 | h12115
                  · rcases h3bigk with h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c | h12116c
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [hlam, p12116_0]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [h7360, hlam, p12116_1]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [h11550, h11558, h11968, h12115, hlam, p12116_2]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [h11553, h11968, h12115, h7360, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p12116_1]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      rcases p12116_3 (m.d 0 3) (by simp) with h12121 | h12121
                      · rcases p12116_3 (m.d 1 3) (by simp) with h12122 | h12122
                        · rcases p12116_3 (m.d 2 3) (by simp) with h12123 | h12123
                          · linarith only [h11548, h12123, hlam]
                          · rcases p12116_3 (m.d 3 4) (by simp) with h12125 | h12125
                            · linarith only [h11550, h12125, hlam]
                            · linarith only [h12115, h12125, hlam]
                        · linarith only [h11556, h12122, hlam]
                      · linarith only [h12121, hlam, p12116_0]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [h11550, h11553, h11558, h11968, h12115, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12116_1]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [hlam, p12116_0]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [h11550, h11558, h11968, h12115, h7360, hlam, p12116_2]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [h11558, h11968, h12115, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12116_1]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      rcases p12116_3 (m.d 0 3) (by simp) with h12134 | h12134
                      · linarith only [h12134, h7360, hlam]
                      · linarith only [h11551, h12134, hlam]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [h11548, hlam, p12116_0]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [h11553, hlam, p12116_0]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [hlam, p12116_0]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [h11558, hlam, p12116_0]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [h11921, hlam, p12116_0]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [h11550, hlam, p12116_0]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [h11555, hlam, p12116_0]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      rcases p12116_3 (m.d 0 3) (by simp) with h12144 | h12144
                      · rcases p12116_3 (m.d 1 3) (by simp) with h12145 | h12145
                        · rcases p12116_3 (m.d 2 3) (by simp) with h12146 | h12146
                          · linarith only [h12146, hlam, p12116_0]
                          · rcases p12116_3 (m.d 3 4) (by simp) with h12148 | h12148
                            · rcases p12116_3 (m.d 3 5) (by simp) with h12149 | h12149
                              · linarith only [h12115, h12149, hlam]
                              · linarith only [h11921, h12149, hlam]
                            · linarith only [h12148, hlam, p12116_0]
                        · linarith only [h11553, h12145, hlam]
                      · linarith only [h11548, h12144, hlam]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [hlam, p12116_0]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [h11550, h11558, h11968, h12115, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12116_1]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [h11551, hlam, p12116_0]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [h11556, hlam, p12116_0]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      rcases p12116_3 (m.d 0 3) (by simp) with h12159 | h12159
                      · rcases p12116_3 (m.d 1 3) (by simp) with h12160 | h12160
                        · rcases p12116_3 (m.d 2 3) (by simp) with h12161 | h12161
                          · linarith only [h12161, hlam, p12116_0]
                          · rcases p12116_3 (m.d 3 4) (by simp) with h12163 | h12163
                            · rcases p12116_3 (m.d 3 5) (by simp) with h12164 | h12164
                              · rcases h4bigk with h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c | h12165c
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [hlam, p12165_0]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h8811, hlam, p12165_0]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  rcases p12165_3 (m.d 0 4) (by simp) with h12168 | h12168
                                  · rcases p12165_3 (m.d 1 4) (by simp) with h12169 | h12169
                                    · rcases p12165_3 (m.d 2 4) (by simp) with h12170 | h12170
                                      · linarith only [h11549, h12170, hlam]
                                      · rcases p12165_3 (m.d 3 4) (by simp) with h12172 | h12172
                                        · linarith only [h11550, h12172, hlam]
                                        · linarith only [h11558, h12172, hlam]
                                    · linarith only [h11554, h12169, hlam]
                                  · linarith only [h11549, h12168, hlam]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h11558, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12165_1]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h11553, h11555, h11558, h11968, h8811, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12165_1]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h11553, h11555, h8811, hc01, hc12, hlam, hphi, p12165_1]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [hlam, p12165_0]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  rcases p12165_3 (m.d 0 4) (by simp) with h12181 | h12181
                                  · linarith only [h12181, h8811, hlam]
                                  · linarith only [h11549, h12181, hlam]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h11553, h11555, h11558, h11968, h12115, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12165_1]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h11553, h11555, h11558, h11968, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12165_1]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h11549, hlam, p12165_1]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h11554, hlam, p12165_1]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [hlam, p12165_0]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h11558, hlam, p12165_1]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h11968, hlam, p12165_0]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h11550, hlam, p12165_1]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h11555, hlam, p12165_0]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h11558, hc23, hc34, hlam, hphi, p12165_1]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [hlam, p12165_0]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h11550, h11553, h11558, h11968, h7360, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12165_1]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h11552, hlam, p12165_0]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h11557, hlam, p12165_0]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h11558, hc23, hc45, hlam, hphi, ht34, p12165_1]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [h12115, hlam, p12165_0]
                                · have p12165_0 := h12165c.1
                                  have p12165_1 := h12165c.2.1
                                  have p12165_2 := h12165c.2.2.1
                                  have p12165_3 := h12165c.2.2.2
                                  linarith only [hlam, p12165_0]
                              · linarith only [h12164, hlam, p12116_0]
                            · linarith only [h11558, h12163, hlam]
                        · linarith only [h11553, h12160, hlam]
                      · linarith only [h11548, h12159, hlam]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [h12115, hlam, p12116_0]
                    · have p12116_0 := h12116c.1
                      have p12116_1 := h12116c.2.1
                      have p12116_2 := h12116c.2.2.1
                      have p12116_3 := h12116c.2.2.2
                      linarith only [hlam, p12116_0]
                  · rcases h3bigk with h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [hlam, p12207_0]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [h7360, hlam, p12207_1]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [h11550, h11552, h11558, h12115, hlam, p12207_2]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      rcases p12207_3 (m.d 0 3) (by simp) with h12211 | h12211
                      · rcases p12207_3 (m.d 1 3) (by simp) with h12212 | h12212
                        · rcases p12207_3 (m.d 2 3) (by simp) with h12213 | h12213
                          · linarith only [h11548, h12213, hlam]
                          · rcases p12207_3 (m.d 3 4) (by simp) with h12215 | h12215
                            · linarith only [h12215, hlam, p12207_0]
                            · rcases p12207_3 (m.d 3 5) (by simp) with h12217 | h12217
                              · linarith only [h11551, h12217, hlam]
                              · linarith only [h12115, h12217, hlam]
                        · linarith only [h11555, h12212, hlam]
                      · linarith only [h12211, hlam, p12207_0]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      rcases p12207_3 (m.d 0 3) (by simp) with h12222 | h12222
                      · rcases p12207_3 (m.d 1 3) (by simp) with h12223 | h12223
                        · rcases p12207_3 (m.d 2 3) (by simp) with h12224 | h12224
                          · linarith only [h11548, h12224, hlam]
                          · rcases p12207_3 (m.d 3 4) (by simp) with h12226 | h12226
                            · linarith only [h11550, h12226, hlam]
                            · rcases p12207_3 (m.d 3 5) (by simp) with h12228 | h12228
                              · linarith only [h12228, hlam, p12207_0]
                              · rcases h4bigk with h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c | h12230c
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [hlam, p12230_0]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h8811, hlam, p12230_0]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  rcases p12230_3 (m.d 0 4) (by simp) with h12233 | h12233
                                  · rcases p12230_3 (m.d 1 4) (by simp) with h12234 | h12234
                                    · rcases p12230_3 (m.d 2 4) (by simp) with h12235 | h12235
                                      · linarith only [h11549, h12235, hlam]
                                      · rcases p12230_3 (m.d 3 4) (by simp) with h12237 | h12237
                                        · linarith only [h11550, h12237, hlam]
                                        · linarith only [h11558, h12237, hlam]
                                    · linarith only [h11554, h12234, hlam]
                                  · linarith only [h11549, h12233, hlam]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h11550, h11558, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12230_1]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h11550, h11553, h11558, h12115, h7360, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12230_1]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h11553, h11555, h8811, hc01, hc12, hlam, hphi, p12230_1]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [hlam, p12230_0]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  rcases p12230_3 (m.d 0 4) (by simp) with h12246 | h12246
                                  · linarith only [h12246, h8811, hlam]
                                  · linarith only [h11549, h12246, hlam]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h11553, h11555, h11558, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12230_1]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h11553, h11555, h11558, h12115, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12230_1]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h11549, hlam, p12230_1]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h11554, hlam, p12230_1]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [hlam, p12230_0]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h11558, hlam, p12230_1]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h11968, hlam, p12230_0]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h11550, hlam, p12230_1]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h11555, hlam, p12230_0]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h11552, h11558, h12115, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12230_1]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [hlam, p12230_0]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h12115, hlam, p12230_0]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h11552, hlam, p12230_0]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h11557, hlam, p12230_0]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h11552, h11553, h11555, h11558, h8811, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12230_1]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [h11552, h11553, h11555, h8811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12230_1]
                                · have p12230_0 := h12230c.1
                                  have p12230_1 := h12230c.2.1
                                  have p12230_2 := h12230c.2.2.1
                                  have p12230_3 := h12230c.2.2.2
                                  linarith only [hlam, p12230_0]
                        · linarith only [h11556, h12223, hlam]
                      · linarith only [h12222, hlam, p12207_0]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [h11550, h11553, h11558, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12207_1]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [hlam, p12207_0]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [h11550, h11552, h11558, h12115, h7360, hlam, p12207_2]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      rcases p12207_3 (m.d 0 3) (by simp) with h12271 | h12271
                      · linarith only [h12271, h7360, hlam]
                      · linarith only [h11550, h12271, hlam]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      rcases p12207_3 (m.d 0 3) (by simp) with h12274 | h12274
                      · linarith only [h12274, h7360, hlam]
                      · linarith only [h11551, h12274, hlam]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [h11548, hlam, p12207_0]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [h11553, hlam, p12207_0]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [hlam, p12207_0]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [h11558, hlam, p12207_0]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [h11921, hlam, p12207_0]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [h11550, hlam, p12207_0]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [h11555, hlam, p12207_0]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [h11550, h11552, h12115, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12207_1]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [hlam, p12207_0]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [h12115, hlam, p12207_1]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [h11551, hlam, p12207_0]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [h11556, hlam, p12207_0]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      rcases p12207_3 (m.d 0 3) (by simp) with h12289 | h12289
                      · rcases p12207_3 (m.d 1 3) (by simp) with h12290 | h12290
                        · rcases p12207_3 (m.d 2 3) (by simp) with h12291 | h12291
                          · linarith only [h12291, hlam, p12207_0]
                          · rcases p12207_3 (m.d 3 4) (by simp) with h12293 | h12293
                            · linarith only [h12115, h12293, hlam]
                            · linarith only [h11558, h12293, hlam]
                        · linarith only [h11553, h12290, hlam]
                      · linarith only [h11548, h12289, hlam]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [h11558, hc23, hc35, hlam, hphi, p12207_1]
                    · have p12207_0 := h12207c.1
                      have p12207_1 := h12207c.2.1
                      have p12207_2 := h12207c.2.2.1
                      have p12207_3 := h12207c.2.2.2
                      linarith only [hlam, p12207_0]
          · linarith only [h0, h11548, h11550, h11552, h11557, h8811, hc01, hc12, hlam, hphi]
        · linarith only [h11551, h11556, h7360, hlam]
      · linarith only [h11550, h11555, h7360, hlam]
    · linarith only [h0, h11549, h11554, hlam]
  · linarith only [h0, h11548, h11553, hlam]

end R2N4
