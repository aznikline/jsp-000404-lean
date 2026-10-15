import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5504000 in
set_option maxHeartbeats 5504000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s15_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11559 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg11560 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11561 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11562 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11563 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h10058 := hg10058
  have h11024 := hg11024
  have h11558 := hg11558
  have h11559 := hg11559
  have h11560 := hg11560
  rcases m.htr 1 2 3 (by decide) (by decide) with h11564 | h11564
  · rcases m.htr 1 2 4 (by decide) (by decide) with h11565 | h11565
    · rcases m.htr 1 2 5 (by decide) (by decide) with h11566 | h11566
      · rcases m.htr 1 3 4 (by decide) (by decide) with h11567 | h11567
        · rcases m.htr 1 4 5 (by decide) (by decide) with h11568 | h11568
          · rcases m.htr 2 3 4 (by decide) (by decide) with h11569 | h11569
            · rcases m.htr 2 3 5 (by decide) (by decide) with h11570 | h11570
              · rcases m.htr 2 4 5 (by decide) (by decide) with h11571 | h11571
                · rcases m.htr 3 4 5 (by decide) (by decide) with h11572 | h11572
                  · linarith only [h11558, h11569, h11572, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h11558, h11569, h11571, h11572, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h11575 | h11575
                  · linarith only [h11558, h11561, h11571, h11575, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases h0bigk with h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c | h11577c
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [hlam, p11577_0]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [h0, hlam, p11577_1]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [h6793, hlam, p11577_0]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [h10058, hlam, p11577_1]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [h11024, hlam, p11577_1]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      rcases p11577_3 (m.d 0 1) (by simp) with h11583 | h11583
                      · linarith only [h0, h11583, hlam]
                      · rcases p11577_3 (m.d 0 2) (by simp) with h11585 | h11585
                        · rcases p11577_3 (m.d 0 3) (by simp) with h11586 | h11586
                          · linarith only [h11558, h11586, hlam]
                          · linarith only [h11586, h6793, hlam]
                        · linarith only [h0, h11585, hlam]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [hlam, p11577_0]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [h11558, h11570, hc35, hlam, hphi, ht0b, ht5b, p11577_1, u0elo1]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [h11563, h11569, h11571, hc34, hlam, hphi, ht0b, ht45, ht5b, p11577_1, u0elo1]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [h11563, h11569, h11571, hc34, hlam, hphi, ht0b, ht45, ht5b, p11577_1, u0elo1]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      rcases p11577_3 (m.d 0 1) (by simp) with h11594 | h11594
                      · linarith only [h11594, h6793, hlam]
                      · rcases p11577_3 (m.d 0 2) (by simp) with h11596 | h11596
                        · rcases p11577_3 (m.d 0 3) (by simp) with h11597 | h11597
                          · rcases p11577_3 (m.d 0 4) (by simp) with h11598 | h11598
                            · linarith only [h11561, h11598, hlam]
                            · linarith only [h10058, h11598, hlam]
                          · linarith only [h11597, h6793, hlam]
                        · linarith only [h0, h11596, hlam]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [h11558, hlam, p11577_1]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [hlam, p11577_0]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [h11558, h11563, h11569, h11571, hc34, hlam, hphi, ht0b, ht45, ht5b, p11577_1, u0elo1]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [h11558, h11563, h11569, h11571, hc34, hlam, hphi, ht0b, ht45, ht5b, p11577_1, u0elo1]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      rcases p11577_3 (m.d 0 1) (by simp) with h11607 | h11607
                      · linarith only [h10058, h11607, hlam]
                      · rcases p11577_3 (m.d 0 2) (by simp) with h11609 | h11609
                        · rcases p11577_3 (m.d 0 3) (by simp) with h11610 | h11610
                          · rcases p11577_3 (m.d 0 4) (by simp) with h11611 | h11611
                            · rcases p11577_3 (m.d 0 5) (by simp) with h11612 | h11612
                              · linarith only [h11563, h11612, hlam]
                              · linarith only [h11024, h11612, hlam]
                            · linarith only [h10058, h11611, hlam]
                          · linarith only [h11610, h6793, hlam]
                        · linarith only [h0, h11609, hlam]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [h11559, hlam, p11577_0]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [h11561, hlam, p11577_0]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [hlam, p11577_0]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [h11558, h11561, h11563, h11569, h11571, hc34, hlam, hphi, ht0b, ht45, ht5b, p11577_1, u0elo1]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      rcases p11577_3 (m.d 0 1) (by simp) with h11622 | h11622
                      · linarith only [h11024, h11622, hlam]
                      · rcases p11577_3 (m.d 0 2) (by simp) with h11624 | h11624
                        · rcases p11577_3 (m.d 0 3) (by simp) with h11625 | h11625
                          · rcases p11577_3 (m.d 0 4) (by simp) with h11626 | h11626
                            · rcases p11577_3 (m.d 0 5) (by simp) with h11627 | h11627
                              · rcases h0emin with h11628 | h11628 | h11628 | h11628 | h11628
                                · linarith only [h11558, h11561, h11563, h11628, hlam, p11577_1, u0elo1]
                                · rcases h2bigk with h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c | h11630c
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [hlam, p11630_0]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [h0, hlam, p11630_1]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [h11569, hc34, hlam, hphi, ht0b, ht45, ht5b, p11630_1, u0elo1]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    rcases p11630_3 (m.d 0 2) (by simp) with h11634 | h11634
                                    · rcases p11630_3 (m.d 1 2) (by simp) with h11635 | h11635
                                      · rcases p11630_3 (m.d 2 3) (by simp) with h11636 | h11636
                                        · linarith only [h11558, h11636, hlam]
                                        · linarith only [h11569, h11636, hlam]
                                      · linarith only [h11565, h11635, hlam]
                                    · linarith only [h11634, hlam, p11630_0]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    rcases p11630_3 (m.d 0 2) (by simp) with h11641 | h11641
                                    · rcases p11630_3 (m.d 1 2) (by simp) with h11642 | h11642
                                      · rcases p11630_3 (m.d 2 3) (by simp) with h11643 | h11643
                                        · linarith only [h11558, h11643, hlam]
                                        · linarith only [h11570, h11643, hlam]
                                      · linarith only [h11566, h11642, hlam]
                                    · linarith only [h11641, hlam, p11630_0]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [h11558, h11561, h11563, hc01, hc12, hlam, hphi, p11577_1, p11630_1]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [hlam, p11630_0]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    rcases p11630_3 (m.d 0 2) (by simp) with h11650 | h11650
                                    · linarith only [h0, h11650, hlam]
                                    · linarith only [h11558, h11650, hlam]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    rcases p11630_3 (m.d 0 2) (by simp) with h11653 | h11653
                                    · linarith only [h0, h11653, hlam]
                                    · linarith only [h11559, h11653, hlam]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    rcases p11630_3 (m.d 0 2) (by simp) with h11656 | h11656
                                    · linarith only [h0, h11656, hlam]
                                    · linarith only [h11560, h11656, hlam]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [h11558, hlam, p11630_0]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [h11564, hlam, p11630_0]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [hlam, p11630_0]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [h11558, h11569, hc34, hlam, hphi, ht0b, ht45, ht5b, p11630_1, u0elo1]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [h11558, hc25, hlam, hphi, ht0b, ht5b, p11630_1, u0elo1]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [h11559, hlam, p11630_0]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [h11565, hlam, p11630_0]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [h11569, hlam, p11630_1]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [hlam, p11630_0]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [h11571, hlam, p11630_1]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [h11560, hlam, p11630_0]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [h11566, hlam, p11630_0]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [h11570, hlam, p11630_1]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [h11560, h11569, hc34, hlam, hphi, ht0b, ht45, ht5b, p11630_1, u0elo1]
                                  · have p11630_0 := h11630c.1
                                    have p11630_1 := h11630c.2.1
                                    have p11630_2 := h11630c.2.2.1
                                    have p11630_3 := h11630c.2.2.2
                                    linarith only [hlam, p11630_0]
                                · rcases h2bigk with h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [hlam, p11674_0]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [h0, hlam, p11674_1]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [h11569, hc34, hlam, hphi, ht0b, ht45, ht5b, p11674_1, u0elo1]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    rcases p11674_3 (m.d 0 2) (by simp) with h11678 | h11678
                                    · rcases p11674_3 (m.d 1 2) (by simp) with h11679 | h11679
                                      · rcases p11674_3 (m.d 2 3) (by simp) with h11680 | h11680
                                        · linarith only [h11558, h11680, hlam]
                                        · linarith only [h11569, h11680, hlam]
                                      · linarith only [h11565, h11679, hlam]
                                    · linarith only [h11678, hlam, p11674_0]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    rcases p11674_3 (m.d 0 2) (by simp) with h11685 | h11685
                                    · rcases p11674_3 (m.d 1 2) (by simp) with h11686 | h11686
                                      · rcases p11674_3 (m.d 2 3) (by simp) with h11687 | h11687
                                        · linarith only [h11558, h11687, hlam]
                                        · linarith only [h11570, h11687, hlam]
                                      · linarith only [h11566, h11686, hlam]
                                    · linarith only [h11685, hlam, p11674_0]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [h11558, h11561, h11563, hc01, hc12, hlam, hphi, p11577_1, p11674_1]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [hlam, p11674_0]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    rcases p11674_3 (m.d 0 2) (by simp) with h11694 | h11694
                                    · linarith only [h0, h11694, hlam]
                                    · linarith only [h11558, h11694, hlam]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    rcases p11674_3 (m.d 0 2) (by simp) with h11697 | h11697
                                    · linarith only [h0, h11697, hlam]
                                    · linarith only [h11559, h11697, hlam]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    rcases p11674_3 (m.d 0 2) (by simp) with h11700 | h11700
                                    · linarith only [h0, h11700, hlam]
                                    · linarith only [h11560, h11700, hlam]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [h11558, hlam, p11674_0]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [h11564, hlam, p11674_0]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [hlam, p11674_0]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [h11558, h11569, hc34, hlam, hphi, ht0b, ht45, ht5b, p11674_1, u0elo1]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [h11558, hc25, hlam, hphi, ht0b, ht5b, p11674_1, u0elo1]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [h11559, hlam, p11674_0]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [h11565, hlam, p11674_0]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [h11569, hlam, p11674_1]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [hlam, p11674_0]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [h11571, hlam, p11674_1]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [h11560, hlam, p11674_0]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [h11566, hlam, p11674_0]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [h11570, hlam, p11674_1]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [h11560, h11569, hc34, hlam, hphi, ht0b, ht45, ht5b, p11674_1, u0elo1]
                                  · have p11674_0 := h11674c.1
                                    have p11674_1 := h11674c.2.1
                                    have p11674_2 := h11674c.2.2.1
                                    have p11674_3 := h11674c.2.2.2
                                    linarith only [hlam, p11674_0]
                                · rcases h2bigk with h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c | h11718c
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [hlam, p11718_0]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [h0, hlam, p11718_1]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [h11569, hc34, hlam, hphi, ht0b, ht45, ht5b, p11718_1, u0elo1]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    rcases p11718_3 (m.d 0 2) (by simp) with h11722 | h11722
                                    · rcases p11718_3 (m.d 1 2) (by simp) with h11723 | h11723
                                      · rcases p11718_3 (m.d 2 3) (by simp) with h11724 | h11724
                                        · linarith only [h11558, h11724, hlam]
                                        · linarith only [h11569, h11724, hlam]
                                      · linarith only [h11565, h11723, hlam]
                                    · linarith only [h11722, hlam, p11718_0]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    rcases p11718_3 (m.d 0 2) (by simp) with h11729 | h11729
                                    · rcases p11718_3 (m.d 1 2) (by simp) with h11730 | h11730
                                      · rcases p11718_3 (m.d 2 3) (by simp) with h11731 | h11731
                                        · linarith only [h11558, h11731, hlam]
                                        · linarith only [h11570, h11731, hlam]
                                      · linarith only [h11566, h11730, hlam]
                                    · linarith only [h11729, hlam, p11718_0]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [h11558, h11561, h11563, hc01, hc12, hlam, hphi, p11577_1, p11718_1]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [hlam, p11718_0]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    rcases p11718_3 (m.d 0 2) (by simp) with h11738 | h11738
                                    · linarith only [h0, h11738, hlam]
                                    · linarith only [h11558, h11738, hlam]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    rcases p11718_3 (m.d 0 2) (by simp) with h11741 | h11741
                                    · linarith only [h0, h11741, hlam]
                                    · linarith only [h11559, h11741, hlam]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    rcases p11718_3 (m.d 0 2) (by simp) with h11744 | h11744
                                    · linarith only [h0, h11744, hlam]
                                    · linarith only [h11560, h11744, hlam]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [h11558, hlam, p11718_0]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [h11564, hlam, p11718_0]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [hlam, p11718_0]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [h11558, h11569, hc34, hlam, hphi, ht0b, ht45, ht5b, p11718_1, u0elo1]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [h11558, hc25, hlam, hphi, ht0b, ht5b, p11718_1, u0elo1]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [h11559, hlam, p11718_0]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [h11565, hlam, p11718_0]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [h11569, hlam, p11718_1]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [hlam, p11718_0]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [h11571, hlam, p11718_1]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [h11560, hlam, p11718_0]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [h11566, hlam, p11718_0]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [h11570, hlam, p11718_1]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [h11560, h11569, hc34, hlam, hphi, ht0b, ht45, ht5b, p11718_1, u0elo1]
                                  · have p11718_0 := h11718c.1
                                    have p11718_1 := h11718c.2.1
                                    have p11718_2 := h11718c.2.2.1
                                    have p11718_3 := h11718c.2.2.2
                                    linarith only [hlam, p11718_0]
                                · rcases h2bigk with h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c | h11762c
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [hlam, p11762_0]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [h0, hlam, p11762_1]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [h11569, hc34, hlam, hphi, ht0b, ht45, ht5b, p11762_1, u0elo1]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    rcases p11762_3 (m.d 0 2) (by simp) with h11766 | h11766
                                    · rcases p11762_3 (m.d 1 2) (by simp) with h11767 | h11767
                                      · rcases p11762_3 (m.d 2 3) (by simp) with h11768 | h11768
                                        · linarith only [h11558, h11768, hlam]
                                        · linarith only [h11569, h11768, hlam]
                                      · linarith only [h11565, h11767, hlam]
                                    · linarith only [h11766, hlam, p11762_0]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    rcases p11762_3 (m.d 0 2) (by simp) with h11773 | h11773
                                    · rcases p11762_3 (m.d 1 2) (by simp) with h11774 | h11774
                                      · rcases p11762_3 (m.d 2 3) (by simp) with h11775 | h11775
                                        · linarith only [h11558, h11775, hlam]
                                        · linarith only [h11570, h11775, hlam]
                                      · linarith only [h11566, h11774, hlam]
                                    · linarith only [h11773, hlam, p11762_0]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [h11558, h11561, h11563, hc01, hc12, hlam, hphi, p11577_1, p11762_1]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [hlam, p11762_0]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    rcases p11762_3 (m.d 0 2) (by simp) with h11782 | h11782
                                    · linarith only [h0, h11782, hlam]
                                    · linarith only [h11558, h11782, hlam]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    rcases p11762_3 (m.d 0 2) (by simp) with h11785 | h11785
                                    · linarith only [h0, h11785, hlam]
                                    · linarith only [h11559, h11785, hlam]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    rcases p11762_3 (m.d 0 2) (by simp) with h11788 | h11788
                                    · linarith only [h0, h11788, hlam]
                                    · linarith only [h11560, h11788, hlam]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [h11558, hlam, p11762_0]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [h11564, hlam, p11762_0]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [hlam, p11762_0]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [h11558, h11569, hc34, hlam, hphi, ht0b, ht45, ht5b, p11762_1, u0elo1]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [h11558, hc25, hlam, hphi, ht0b, ht5b, p11762_1, u0elo1]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [h11559, hlam, p11762_0]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [h11565, hlam, p11762_0]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [h11569, hlam, p11762_1]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [hlam, p11762_0]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [h11571, hlam, p11762_1]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [h11560, hlam, p11762_0]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [h11566, hlam, p11762_0]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [h11570, hlam, p11762_1]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [h11560, h11569, hc34, hlam, hphi, ht0b, ht45, ht5b, p11762_1, u0elo1]
                                  · have p11762_0 := h11762c.1
                                    have p11762_1 := h11762c.2.1
                                    have p11762_2 := h11762c.2.2.1
                                    have p11762_3 := h11762c.2.2.2
                                    linarith only [hlam, p11762_0]
                              · linarith only [h11024, h11627, hlam]
                            · linarith only [h10058, h11626, hlam]
                          · linarith only [h11625, h6793, hlam]
                        · linarith only [h0, h11624, hlam]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [h11560, hlam, p11577_1]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [h11562, hlam, p11577_0]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [h11563, hlam, p11577_1]
                    · have p11577_0 := h11577c.1
                      have p11577_1 := h11577c.2.1
                      have p11577_2 := h11577c.2.2.1
                      have p11577_3 := h11577c.2.2.2
                      linarith only [hlam, p11577_0]
              · linarith only [h11558, h11562, h11569, h11570, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h11815 | h11815
              · linarith only [h11558, h11561, h11569, h11815, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h11817 | h11817
                · rcases m.htr 3 4 5 (by decide) (by decide) with h11818 | h11818
                  · rcases h0bigk with h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h0, hlam, p11819_1]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h6793, hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h10058, hlam, p11819_1]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11024, hlam, p11819_1]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      rcases p11819_3 (m.d 0 1) (by simp) with h11825 | h11825
                      · linarith only [h0, h11825, hlam]
                      · rcases p11819_3 (m.d 0 2) (by simp) with h11827 | h11827
                        · rcases p11819_3 (m.d 0 3) (by simp) with h11828 | h11828
                          · linarith only [h11558, h11828, hlam]
                          · linarith only [h11828, h6793, hlam]
                        · linarith only [h0, h11827, hlam]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11561, h11815, h11818, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11819_1, u0elo1]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11559, h11817, hc45, hlam, hphi, ht0b, ht5b, p11819_1, u0elo1]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11562, h11815, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11819_1, u0elo1]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      rcases p11819_3 (m.d 0 1) (by simp) with h11836 | h11836
                      · linarith only [h11836, h6793, hlam]
                      · rcases p11819_3 (m.d 0 2) (by simp) with h11838 | h11838
                        · rcases p11819_3 (m.d 0 3) (by simp) with h11839 | h11839
                          · rcases p11819_3 (m.d 0 4) (by simp) with h11840 | h11840
                            · linarith only [h11561, h11840, hlam]
                            · linarith only [h10058, h11840, hlam]
                          · linarith only [h11839, h6793, hlam]
                        · linarith only [h0, h11838, hlam]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11558, hlam, p11819_1]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11561, h11815, h11818, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11819_1, u0elo2]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11558, h11562, h11815, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11819_1, u0elo1]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      rcases p11819_3 (m.d 0 1) (by simp) with h11849 | h11849
                      · linarith only [h10058, h11849, hlam]
                      · rcases p11819_3 (m.d 0 2) (by simp) with h11851 | h11851
                        · rcases p11819_3 (m.d 0 3) (by simp) with h11852 | h11852
                          · rcases p11819_3 (m.d 0 4) (by simp) with h11853 | h11853
                            · rcases p11819_3 (m.d 0 5) (by simp) with h11854 | h11854
                              · linarith only [h11563, h11854, hlam]
                              · linarith only [h11024, h11854, hlam]
                            · linarith only [h10058, h11853, hlam]
                          · linarith only [h11852, h6793, hlam]
                        · linarith only [h0, h11851, hlam]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11559, hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11561, hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11562, h11815, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11819_1, u0elo3]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      rcases p11819_3 (m.d 0 1) (by simp) with h11864 | h11864
                      · linarith only [h11024, h11864, hlam]
                      · rcases p11819_3 (m.d 0 2) (by simp) with h11866 | h11866
                        · rcases p11819_3 (m.d 0 3) (by simp) with h11867 | h11867
                          · rcases p11819_3 (m.d 0 4) (by simp) with h11868 | h11868
                            · rcases p11819_3 (m.d 0 5) (by simp) with h11869 | h11869
                              · rcases h0emin with h11870 | h11870 | h11870 | h11870 | h11870
                                · linarith only [h11870, hlam, p11819_1, u0elo4]
                                · rcases h2bigk with h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c | h11872c
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [hlam, p11872_0]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [h0, hlam, p11872_1]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    rcases p11872_3 (m.d 0 2) (by simp) with h11875 | h11875
                                    · rcases p11872_3 (m.d 1 2) (by simp) with h11876 | h11876
                                      · rcases p11872_3 (m.d 2 3) (by simp) with h11877 | h11877
                                        · linarith only [h11877, hlam, p11872_0]
                                        · rcases p11872_3 (m.d 2 4) (by simp) with h11879 | h11879
                                          · linarith only [h11559, h11879, hlam]
                                          · linarith only [h11569, h11879, hlam]
                                      · linarith only [h11564, h11876, hlam]
                                    · linarith only [h11875, hlam, p11872_0]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [h11817, hc45, hlam, hphi, ht0b, ht5b, p11872_1, u0elo1]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    rcases p11872_3 (m.d 0 2) (by simp) with h11885 | h11885
                                    · rcases p11872_3 (m.d 1 2) (by simp) with h11886 | h11886
                                      · rcases p11872_3 (m.d 2 3) (by simp) with h11887 | h11887
                                        · linarith only [h11558, h11887, hlam]
                                        · rcases p11872_3 (m.d 2 4) (by simp) with h11889 | h11889
                                          · linarith only [h11559, h11889, hlam]
                                          · linarith only [h11817, h11889, hlam]
                                      · linarith only [h11566, h11886, hlam]
                                    · linarith only [h11885, hlam, p11872_0]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [h11558, h11561, h11563, hc01, hc12, hlam, hphi, p11819_1, p11872_1]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [hlam, p11872_0]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    rcases p11872_3 (m.d 0 2) (by simp) with h11896 | h11896
                                    · linarith only [h0, h11896, hlam]
                                    · linarith only [h11558, h11896, hlam]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    rcases p11872_3 (m.d 0 2) (by simp) with h11899 | h11899
                                    · linarith only [h0, h11899, hlam]
                                    · linarith only [h11559, h11899, hlam]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    rcases p11872_3 (m.d 0 2) (by simp) with h11902 | h11902
                                    · linarith only [h0, h11902, hlam]
                                    · linarith only [h11560, h11902, hlam]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [h11558, hlam, p11872_0]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [h11564, hlam, p11872_0]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [hlam, p11872_0]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [h11569, hlam, p11872_0]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [h11815, hlam, p11872_0]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [h11559, hlam, p11872_0]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [h11565, hlam, p11872_0]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [h11559, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11872_1, u0elo1]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [hlam, p11872_0]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [h11559, hc25, hlam, hphi, ht0b, ht5b, p11872_1, u0elo1]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [h11560, hlam, p11872_0]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [h11566, hlam, p11872_0]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [h11560, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11872_1, u0elo1]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [h11817, hlam, p11872_0]
                                  · have p11872_0 := h11872c.1
                                    have p11872_1 := h11872c.2.1
                                    have p11872_2 := h11872c.2.2.1
                                    have p11872_3 := h11872c.2.2.2
                                    linarith only [hlam, p11872_0]
                                · rcases h2bigk with h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c | h11920c
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [hlam, p11920_0]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [h0, hlam, p11920_1]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    rcases p11920_3 (m.d 0 2) (by simp) with h11923 | h11923
                                    · rcases p11920_3 (m.d 1 2) (by simp) with h11924 | h11924
                                      · rcases p11920_3 (m.d 2 3) (by simp) with h11925 | h11925
                                        · linarith only [h11925, hlam, p11920_0]
                                        · rcases p11920_3 (m.d 2 4) (by simp) with h11927 | h11927
                                          · linarith only [h11559, h11927, hlam]
                                          · linarith only [h11569, h11927, hlam]
                                      · linarith only [h11564, h11924, hlam]
                                    · linarith only [h11923, hlam, p11920_0]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [h11817, hc45, hlam, hphi, ht0b, ht5b, p11920_1, u0elo1]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    rcases p11920_3 (m.d 0 2) (by simp) with h11933 | h11933
                                    · rcases p11920_3 (m.d 1 2) (by simp) with h11934 | h11934
                                      · rcases p11920_3 (m.d 2 3) (by simp) with h11935 | h11935
                                        · linarith only [h11558, h11935, hlam]
                                        · rcases p11920_3 (m.d 2 4) (by simp) with h11937 | h11937
                                          · linarith only [h11559, h11937, hlam]
                                          · linarith only [h11817, h11937, hlam]
                                      · linarith only [h11566, h11934, hlam]
                                    · linarith only [h11933, hlam, p11920_0]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [h11558, h11561, h11563, hc01, hc12, hlam, hphi, p11819_1, p11920_1]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [hlam, p11920_0]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    rcases p11920_3 (m.d 0 2) (by simp) with h11944 | h11944
                                    · linarith only [h0, h11944, hlam]
                                    · linarith only [h11558, h11944, hlam]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    rcases p11920_3 (m.d 0 2) (by simp) with h11947 | h11947
                                    · linarith only [h0, h11947, hlam]
                                    · linarith only [h11559, h11947, hlam]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    rcases p11920_3 (m.d 0 2) (by simp) with h11950 | h11950
                                    · linarith only [h0, h11950, hlam]
                                    · linarith only [h11560, h11950, hlam]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [h11558, hlam, p11920_0]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [h11564, hlam, p11920_0]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [hlam, p11920_0]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [h11569, hlam, p11920_0]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [h11815, hlam, p11920_0]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [h11559, hlam, p11920_0]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [h11565, hlam, p11920_0]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [h11559, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11920_1, u0elo1]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [hlam, p11920_0]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [h11558, h11561, h11569, hc25, hlam, hphi, ht0b, ht5b, p11920_1, u0elo1]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [h11560, hlam, p11920_0]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [h11566, hlam, p11920_0]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [h11560, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11920_1, u0elo1]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [h11817, hlam, p11920_0]
                                  · have p11920_0 := h11920c.1
                                    have p11920_1 := h11920c.2.1
                                    have p11920_2 := h11920c.2.2.1
                                    have p11920_3 := h11920c.2.2.2
                                    linarith only [hlam, p11920_0]
                                · rcases h2bigk with h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h0, hlam, p11968_1]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    rcases p11968_3 (m.d 0 2) (by simp) with h11971 | h11971
                                    · rcases p11968_3 (m.d 1 2) (by simp) with h11972 | h11972
                                      · rcases p11968_3 (m.d 2 3) (by simp) with h11973 | h11973
                                        · linarith only [h11973, hlam, p11968_0]
                                        · rcases p11968_3 (m.d 2 4) (by simp) with h11975 | h11975
                                          · linarith only [h11559, h11975, hlam]
                                          · linarith only [h11569, h11975, hlam]
                                      · linarith only [h11564, h11972, hlam]
                                    · linarith only [h11971, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11817, hc45, hlam, hphi, ht0b, ht5b, p11968_1, u0elo1]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    rcases p11968_3 (m.d 0 2) (by simp) with h11981 | h11981
                                    · rcases p11968_3 (m.d 1 2) (by simp) with h11982 | h11982
                                      · rcases p11968_3 (m.d 2 3) (by simp) with h11983 | h11983
                                        · linarith only [h11558, h11983, hlam]
                                        · rcases p11968_3 (m.d 2 4) (by simp) with h11985 | h11985
                                          · linarith only [h11559, h11985, hlam]
                                          · linarith only [h11817, h11985, hlam]
                                      · linarith only [h11566, h11982, hlam]
                                    · linarith only [h11981, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11558, h11561, h11563, hc01, hc12, hlam, hphi, p11819_1, p11968_1]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    rcases p11968_3 (m.d 0 2) (by simp) with h11992 | h11992
                                    · linarith only [h0, h11992, hlam]
                                    · linarith only [h11558, h11992, hlam]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    rcases p11968_3 (m.d 0 2) (by simp) with h11995 | h11995
                                    · linarith only [h0, h11995, hlam]
                                    · linarith only [h11559, h11995, hlam]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    rcases p11968_3 (m.d 0 2) (by simp) with h11998 | h11998
                                    · linarith only [h0, h11998, hlam]
                                    · linarith only [h11560, h11998, hlam]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11558, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11564, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11569, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11815, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11559, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11565, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11559, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11968_1, u0elo1]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11558, h11561, h11569, hc25, hlam, hphi, ht0b, ht5b, p11968_1, u0elo1]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11560, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11566, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11560, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11968_1, u0elo1]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11817, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [hlam, p11968_0]
                                · rcases h2bigk with h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c | h12016c
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [hlam, p12016_0]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [h0, hlam, p12016_1]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    rcases p12016_3 (m.d 0 2) (by simp) with h12019 | h12019
                                    · rcases p12016_3 (m.d 1 2) (by simp) with h12020 | h12020
                                      · rcases p12016_3 (m.d 2 3) (by simp) with h12021 | h12021
                                        · linarith only [h12021, hlam, p12016_0]
                                        · rcases p12016_3 (m.d 2 4) (by simp) with h12023 | h12023
                                          · linarith only [h11559, h12023, hlam]
                                          · linarith only [h11569, h12023, hlam]
                                      · linarith only [h11564, h12020, hlam]
                                    · linarith only [h12019, hlam, p12016_0]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [h11817, hc45, hlam, hphi, ht0b, ht5b, p12016_1, u0elo1]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    rcases p12016_3 (m.d 0 2) (by simp) with h12029 | h12029
                                    · rcases p12016_3 (m.d 1 2) (by simp) with h12030 | h12030
                                      · rcases p12016_3 (m.d 2 3) (by simp) with h12031 | h12031
                                        · linarith only [h11558, h12031, hlam]
                                        · rcases p12016_3 (m.d 2 4) (by simp) with h12033 | h12033
                                          · linarith only [h11559, h12033, hlam]
                                          · linarith only [h11817, h12033, hlam]
                                      · linarith only [h11566, h12030, hlam]
                                    · linarith only [h12029, hlam, p12016_0]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [h11558, h11561, h11563, hc01, hc12, hlam, hphi, p11819_1, p12016_1]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [hlam, p12016_0]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    rcases p12016_3 (m.d 0 2) (by simp) with h12040 | h12040
                                    · linarith only [h0, h12040, hlam]
                                    · linarith only [h11558, h12040, hlam]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    rcases p12016_3 (m.d 0 2) (by simp) with h12043 | h12043
                                    · linarith only [h0, h12043, hlam]
                                    · linarith only [h11559, h12043, hlam]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    rcases p12016_3 (m.d 0 2) (by simp) with h12046 | h12046
                                    · linarith only [h0, h12046, hlam]
                                    · linarith only [h11560, h12046, hlam]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [h11558, hlam, p12016_0]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [h11564, hlam, p12016_0]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [hlam, p12016_0]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [h11569, hlam, p12016_0]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [h11815, hlam, p12016_0]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [h11559, hlam, p12016_0]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [h11565, hlam, p12016_0]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [h11559, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12016_1, u0elo1]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [hlam, p12016_0]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [h11558, h11561, h11569, hc25, hlam, hphi, ht0b, ht5b, p12016_1, u0elo1]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [h11560, hlam, p12016_0]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [h11566, hlam, p12016_0]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [h11560, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12016_1, u0elo1]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [h11817, hlam, p12016_0]
                                  · have p12016_0 := h12016c.1
                                    have p12016_1 := h12016c.2.1
                                    have p12016_2 := h12016c.2.2.1
                                    have p12016_3 := h12016c.2.2.2
                                    linarith only [hlam, p12016_0]
                              · linarith only [h11024, h11869, hlam]
                            · linarith only [h10058, h11868, hlam]
                          · linarith only [h11867, h6793, hlam]
                        · linarith only [h0, h11866, hlam]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11560, hlam, p11819_1]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11562, hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11563, hlam, p11819_1]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [hlam, p11819_0]
                  · linarith only [h11558, h11561, h11563, h11569, h11818, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h12073 | h12073
                  · linarith only [h11558, h11561, h11817, h12073, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h11558, h11561, h11563, h11569, h12073, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
          · linarith only [h10058, h11563, h11568, hlam]
        · linarith only [h11561, h11567, h6793, hlam]
      · linarith only [h0, h11560, h11566, hlam]
    · linarith only [h0, h11559, h11565, hlam]
  · linarith only [h0, h11558, h11564, hlam]

end R2N4
