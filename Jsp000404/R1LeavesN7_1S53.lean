import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x4 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h18648 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 1) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 1) ∧ (m.d 0 5) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 5) ≤ z)))
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
  have h15532 := hg15532
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  rcases p18659_3 (m.d 0 1) (by simp) with h18674 | h18674
  · rcases p18659_3 (m.d 0 2) (by simp) with h18675 | h18675
    · rcases p18659_3 (m.d 0 3) (by simp) with h18676 | h18676
      · rcases p18659_3 (m.d 0 4) (by simp) with h18677 | h18677
        · linarith only [h18443, h18677, hlam]
        · rcases p18659_3 (m.d 0 5) (by simp) with h18679 | h18679
          · linarith only [h18444, h18679, hlam]
          · rcases h2bigk with h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c | h18681c
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [hlam, p18681_0]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [h0, hlam, p18681_1]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              rcases p18681_3 (m.d 0 2) (by simp) with h18684 | h18684
              · rcases p18681_3 (m.d 1 2) (by simp) with h18685 | h18685
                · rcases p18681_3 (m.d 2 3) (by simp) with h18686 | h18686
                  · linarith only [h18686, hlam, p18681_0]
                  · rcases p18681_3 (m.d 2 4) (by simp) with h18688 | h18688
                    · linarith only [h18446, h18688, hlam]
                    · rcases p18681_3 (m.d 2 5) (by simp) with h18690 | h18690
                      · linarith only [h18447, h18690, hlam]
                      · rcases h3bigk with h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c | h18692c
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [hlam, p18692_0]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [h15532, hlam, p18692_1]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          rcases p18692_3 (m.d 0 3) (by simp) with h18695 | h18695
                          · rcases p18692_3 (m.d 1 3) (by simp) with h18696 | h18696
                            · rcases p18692_3 (m.d 2 3) (by simp) with h18697 | h18697
                              · linarith only [h18445, h18697, hlam]
                              · rcases p18692_3 (m.d 3 4) (by simp) with h18699 | h18699
                                · linarith only [h18448, h18699, hlam]
                                · rcases p18692_3 (m.d 3 5) (by simp) with h18701 | h18701
                                  · linarith only [h18449, h18701, hlam]
                                  · rcases h5bigk with h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c | h18703c
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [hlam, p18703_0]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [hc01, hc15, hlam, hphi, ht0b, ht5b, p18659_1, p18703_1]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h15532, h18646, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p18659_1, p18703_1]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h15532, h18646, h18657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p18703_1]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h18450, hlam, p18703_1]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h18444, hlam, p18703_0]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [hlam, p18703_0]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h15532, h18444, h18646, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p18703_1]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h15532, h18444, h18646, h18657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p18703_1]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h18651, hlam, p18703_1]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h18447, hlam, p18703_1]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h18648, hlam, p18703_1]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [hlam, p18703_0]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h18447, h18657, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p18703_1]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h18655, hlam, p18703_1]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h18449, hlam, p18703_0]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h18650, hlam, p18703_0]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h18654, hlam, p18703_0]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [hlam, p18703_0]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h18657, hlam, p18703_1]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h18450, hc04, hc45, hlam, hphi, p18703_1]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h18650, h18657, hc34, hc45, hlam, hphi, p18703_1]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h18654, h18657, hc34, hc45, hlam, hphi, p18703_1]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [h18657, hc34, hc45, hlam, hphi, p18703_1]
                                    · have p18703_0 := h18703c.1
                                      have p18703_1 := h18703c.2.1
                                      have p18703_2 := h18703c.2.2.1
                                      have p18703_3 := h18703c.2.2.2
                                      linarith only [hlam, p18703_0]
                            · linarith only [h18646, h18696, hlam]
                          · linarith only [h18445, h18695, hlam]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          rcases p18692_3 (m.d 0 3) (by simp) with h18731 | h18731
                          · rcases p18692_3 (m.d 1 3) (by simp) with h18732 | h18732
                            · rcases p18692_3 (m.d 2 3) (by simp) with h18733 | h18733
                              · linarith only [h18445, h18733, hlam]
                              · linarith only [h18653, h18733, hlam]
                            · linarith only [h18649, h18732, hlam]
                          · linarith only [h18731, hlam, p18692_0]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          rcases p18692_3 (m.d 0 3) (by simp) with h18738 | h18738
                          · rcases p18692_3 (m.d 1 3) (by simp) with h18739 | h18739
                            · rcases p18692_3 (m.d 2 3) (by simp) with h18740 | h18740
                              · linarith only [h18445, h18740, hlam]
                              · linarith only [h18654, h18740, hlam]
                            · linarith only [h18650, h18739, hlam]
                          · linarith only [h18738, hlam, p18692_0]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [h15532, h18443, h18450, h18646, h18647, h18653, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p18692_1]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [hlam, p18692_0]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          rcases p18692_3 (m.d 0 3) (by simp) with h18747 | h18747
                          · linarith only [h15532, h18747, hlam]
                          · linarith only [h18445, h18747, hlam]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [h15532, h18443, h18450, h18647, h18653, hlam, p18659_1, p18692_2]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [h15532, h18447, h18654, hlam, p18659_1, p18692_2]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [h18445, hlam, p18692_0]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [h18646, hlam, p18692_0]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [hlam, p18692_0]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18681_1, p18692_1]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p18681_1, p18692_1]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [h18448, hlam, p18692_0]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [h18649, hlam, p18692_0]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [h18653, hlam, p18692_0]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [hlam, p18692_0]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [h18657, hlam, p18692_1]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [h18449, hlam, p18692_0]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [h18650, hlam, p18692_0]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [h18654, hlam, p18692_0]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [h18449, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p18659_1, p18692_1]
                        · have p18692_0 := h18692c.1
                          have p18692_1 := h18692c.2.1
                          have p18692_2 := h18692c.2.2.1
                          have p18692_3 := h18692c.2.2.2
                          linarith only [hlam, p18692_0]
                · linarith only [h18646, h18685, hlam]
              · linarith only [h18684, hlam, p18681_0]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              rcases p18681_3 (m.d 0 2) (by simp) with h18769 | h18769
              · rcases p18681_3 (m.d 1 2) (by simp) with h18770 | h18770
                · rcases p18681_3 (m.d 2 3) (by simp) with h18771 | h18771
                  · linarith only [h18445, h18771, hlam]
                  · linarith only [h18653, h18771, hlam]
                · linarith only [h18647, h18770, hlam]
              · linarith only [h18769, hlam, p18681_0]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              rcases p18681_3 (m.d 0 2) (by simp) with h18776 | h18776
              · rcases p18681_3 (m.d 1 2) (by simp) with h18777 | h18777
                · rcases p18681_3 (m.d 2 3) (by simp) with h18778 | h18778
                  · linarith only [h18445, h18778, hlam]
                  · linarith only [h18654, h18778, hlam]
                · linarith only [h18648, h18777, hlam]
              · linarith only [h18776, hlam, p18681_0]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p18659_1, p18681_1]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [hlam, p18681_0]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              rcases p18681_3 (m.d 0 2) (by simp) with h18785 | h18785
              · linarith only [h0, h18785, hlam]
              · linarith only [h18445, h18785, hlam]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [h0, h18443, h18450, h18647, hlam, p18659_1, p18681_2]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [h15532, h18447, h18646, hlam, p18659_1, p18681_2]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [h18445, hlam, p18681_0]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [h18646, hlam, p18681_0]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [hlam, p18681_0]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              rcases p18681_3 (m.d 0 2) (by simp) with h18793 | h18793
              · rcases p18681_3 (m.d 1 2) (by simp) with h18794 | h18794
                · rcases p18681_3 (m.d 2 3) (by simp) with h18795 | h18795
                  · rcases p18681_3 (m.d 2 4) (by simp) with h18796 | h18796
                    · linarith only [h18653, h18796, hlam]
                    · rcases p18681_3 (m.d 2 5) (by simp) with h18798 | h18798
                      · linarith only [h18654, h18798, hlam]
                      · linarith only [h18655, h18798, hlam]
                  · linarith only [h18653, h18795, hlam]
                · linarith only [h18647, h18794, hlam]
              · linarith only [h18446, h18793, hlam]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              rcases p18681_3 (m.d 0 2) (by simp) with h18804 | h18804
              · rcases p18681_3 (m.d 1 2) (by simp) with h18805 | h18805
                · rcases p18681_3 (m.d 2 3) (by simp) with h18806 | h18806
                  · rcases p18681_3 (m.d 2 4) (by simp) with h18807 | h18807
                    · linarith only [h18653, h18807, hlam]
                    · rcases p18681_3 (m.d 2 5) (by simp) with h18809 | h18809
                      · linarith only [h18654, h18809, hlam]
                      · rcases h3bigk with h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c | h18811c
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [hlam, p18811_0]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [h15532, hlam, p18811_1]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [h18654, h18657, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p18681_1, p18811_1]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          rcases p18811_3 (m.d 0 3) (by simp) with h18815 | h18815
                          · rcases p18811_3 (m.d 1 3) (by simp) with h18816 | h18816
                            · rcases p18811_3 (m.d 2 3) (by simp) with h18817 | h18817
                              · linarith only [h18445, h18817, hlam]
                              · linarith only [h18653, h18817, hlam]
                            · linarith only [h18649, h18816, hlam]
                          · linarith only [h18815, hlam, p18811_0]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          rcases p18811_3 (m.d 0 3) (by simp) with h18822 | h18822
                          · rcases p18811_3 (m.d 1 3) (by simp) with h18823 | h18823
                            · rcases p18811_3 (m.d 2 3) (by simp) with h18824 | h18824
                              · linarith only [h18445, h18824, hlam]
                              · linarith only [h18654, h18824, hlam]
                            · linarith only [h18650, h18823, hlam]
                          · linarith only [h18822, hlam, p18811_0]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [h15532, h18443, h18450, h18646, h18647, h18653, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p18811_1]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [hlam, p18811_0]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [h18646, h18654, h18657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18681_1, p18811_1]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [h15532, h18443, h18450, h18647, h18653, hlam, p18659_1, p18811_2]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [h15532, h18447, h18654, hlam, p18659_1, p18811_2]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [h18445, hlam, p18811_0]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [h18646, hlam, p18811_0]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [hlam, p18811_0]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          rcases p18811_3 (m.d 0 3) (by simp) with h18837 | h18837
                          · rcases p18811_3 (m.d 1 3) (by simp) with h18838 | h18838
                            · rcases p18811_3 (m.d 2 3) (by simp) with h18839 | h18839
                              · rcases p18811_3 (m.d 3 4) (by simp) with h18840 | h18840
                                · linarith only [h18840, hlam, p18811_0]
                                · rcases p18811_3 (m.d 3 5) (by simp) with h18842 | h18842
                                  · linarith only [h18654, h18842, hlam]
                                  · linarith only [h18657, h18842, hlam]
                              · linarith only [h18839, hlam, p18811_0]
                            · linarith only [h18649, h18838, hlam]
                          · linarith only [h18448, h18837, hlam]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          rcases p18811_3 (m.d 0 3) (by simp) with h18848 | h18848
                          · rcases p18811_3 (m.d 1 3) (by simp) with h18849 | h18849
                            · rcases p18811_3 (m.d 2 3) (by simp) with h18850 | h18850
                              · rcases p18811_3 (m.d 3 4) (by simp) with h18851 | h18851
                                · linarith only [h18653, h18851, hlam]
                                · rcases p18811_3 (m.d 3 5) (by simp) with h18853 | h18853
                                  · linarith only [h18853, hlam, p18811_0]
                                  · rcases h5bigk with h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [hlam, p18855_0]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [hc01, hc15, hlam, hphi, ht0b, ht5b, p18659_1, p18855_1]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h15532, h18654, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p18659_1, p18855_1]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h15532, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p18659_1, p18855_1]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h18450, hlam, p18855_1]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h18444, hlam, p18855_0]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [hlam, p18855_0]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h15532, h18444, h18654, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p18855_1]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h15532, h18444, h18646, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p18659_1, p18855_1]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h18651, hlam, p18855_1]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h18447, hlam, p18855_1]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h18648, hlam, p18855_1]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [hlam, p18855_0]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h18445, hc02, hc35, hlam, hphi, ht0b, ht5b, p18681_1, p18855_1]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h18655, hlam, p18855_1]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h18449, hlam, p18855_0]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h18650, hlam, p18855_0]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h18654, hlam, p18855_0]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [hlam, p18855_0]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h18657, hlam, p18855_1]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h18443, h18450, h18647, h18653, hc34, hc45, hlam, hphi, p18855_1]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h18647, h18651, h18653, hc34, hc45, hlam, hphi, p18855_1]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h18653, h18655, hc34, hc45, hlam, hphi, p18855_1]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [h18657, hc34, hc45, hlam, hphi, p18855_1]
                                    · have p18855_0 := h18855c.1
                                      have p18855_1 := h18855c.2.1
                                      have p18855_2 := h18855c.2.2.1
                                      have p18855_3 := h18855c.2.2.2
                                      linarith only [hlam, p18855_0]
                              · linarith only [h18850, hlam, p18811_0]
                            · linarith only [h18650, h18849, hlam]
                          · linarith only [h18449, h18848, hlam]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [h18448, hlam, p18811_0]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [h18649, hlam, p18811_0]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [h18653, hlam, p18811_0]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [hlam, p18811_0]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [h18657, hlam, p18811_1]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [h18449, hlam, p18811_0]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [h18650, hlam, p18811_0]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [h18654, hlam, p18811_0]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [h15532, h18449, h18646, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p18811_1]
                        · have p18811_0 := h18811c.1
                          have p18811_1 := h18811c.2.1
                          have p18811_2 := h18811c.2.2.1
                          have p18811_3 := h18811c.2.2.2
                          linarith only [hlam, p18811_0]
                  · linarith only [h18654, h18806, hlam]
                · linarith only [h18648, h18805, hlam]
              · linarith only [h18447, h18804, hlam]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [h18446, hlam, p18681_0]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [h18647, hlam, p18681_0]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [h18653, hlam, p18681_1]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [hlam, p18681_0]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [h18655, hlam, p18681_1]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [h18447, hlam, p18681_0]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [h18648, hlam, p18681_0]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [h18654, hlam, p18681_1]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [h15532, h18447, h18646, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p18681_1]
            · have p18681_0 := h18681c.1
              have p18681_1 := h18681c.2.1
              have p18681_2 := h18681c.2.2.1
              have p18681_3 := h18681c.2.2.2
              linarith only [hlam, p18681_0]
      · linarith only [h18449, h18676, hlam]
    · linarith only [h18447, h18675, hlam]
  · linarith only [h18444, h18674, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x5 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h18648 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 2) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 2) ∧ (m.d 0 1) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 1) ≤ z)))
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
  have h15532 := hg15532
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  rcases p18659_3 (m.d 0 1) (by simp) with h18910 | h18910
  · linarith only [h0, h18910, hlam]
  · rcases p18659_3 (m.d 0 2) (by simp) with h18912 | h18912
    · rcases p18659_3 (m.d 0 3) (by simp) with h18913 | h18913
      · linarith only [h18445, h18913, hlam]
      · linarith only [h15532, h18913, hlam]
    · linarith only [h0, h18912, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x6 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h18648 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 2) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 2) ∧ (m.d 0 2) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 2) ≤ z)))
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
  have h15532 := hg15532
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  linarith only [hlam, p18659_0]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x7 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h18648 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 2) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 2) ∧ (m.d 0 3) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 3) ≤ z)))
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
  have h15532 := hg15532
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  rcases p18659_3 (m.d 0 1) (by simp) with h18918 | h18918
  · linarith only [h0, h18918, hlam]
  · rcases p18659_3 (m.d 0 2) (by simp) with h18920 | h18920
    · rcases p18659_3 (m.d 0 3) (by simp) with h18921 | h18921
      · linarith only [h18445, h18921, hlam]
      · rcases p18659_3 (m.d 0 4) (by simp) with h18923 | h18923
        · linarith only [h18446, h18923, hlam]
        · rcases p18659_3 (m.d 0 5) (by simp) with h18925 | h18925
          · linarith only [h18447, h18925, hlam]
          · rcases h2bigk with h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c | h18927c
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [hlam, p18927_0]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h0, hlam, p18927_1]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              rcases p18927_3 (m.d 0 2) (by simp) with h18930 | h18930
              · rcases p18927_3 (m.d 1 2) (by simp) with h18931 | h18931
                · rcases p18927_3 (m.d 2 3) (by simp) with h18932 | h18932
                  · linarith only [h18932, hlam, p18927_0]
                  · rcases p18927_3 (m.d 2 4) (by simp) with h18934 | h18934
                    · linarith only [h18446, h18934, hlam]
                    · rcases p18927_3 (m.d 2 5) (by simp) with h18936 | h18936
                      · linarith only [h18447, h18936, hlam]
                      · rcases h3bigk with h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c | h18938c
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [hlam, p18938_0]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [h15532, hlam, p18938_1]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [h0, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p18659_1, p18938_1]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p18938_1]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p18659_1, p18938_1]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          rcases p18938_3 (m.d 0 3) (by simp) with h18944 | h18944
                          · linarith only [h15532, h18944, hlam]
                          · rcases p18938_3 (m.d 1 3) (by simp) with h18946 | h18946
                            · rcases p18938_3 (m.d 2 3) (by simp) with h18947 | h18947
                              · linarith only [h18646, h18947, hlam]
                              · rcases p18938_3 (m.d 3 4) (by simp) with h18949 | h18949
                                · linarith only [h18649, h18949, hlam]
                                · rcases p18938_3 (m.d 3 5) (by simp) with h18951 | h18951
                                  · linarith only [h18650, h18951, hlam]
                                  · rcases h5bigk with h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c | h18953c
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [hlam, p18953_0]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h0, h15532, h18444, h18647, h18651, h18653, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p18953_1]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h0, h15532, h18444, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p18659_1, p18953_1]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h0, h15532, h18444, h18657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p18953_1]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h18450, hlam, p18953_1]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h18444, hlam, p18953_0]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [hlam, p18953_0]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h0, h15532, h18444, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p18659_1, p18953_1]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h0, h15532, h18444, h18657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p18953_1]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h18651, hlam, p18953_1]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h18447, hlam, p18953_1]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h18648, hlam, p18953_1]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [hlam, p18953_0]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h0, h18447, h18657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18953_1]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h18655, hlam, p18953_1]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h18449, hlam, p18953_0]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h18650, hlam, p18953_0]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h18654, hlam, p18953_0]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [hlam, p18953_0]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h18657, hlam, p18953_1]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h18449, h18657, hc34, hc45, hlam, hphi, p18953_1]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h18650, h18657, hc34, hc45, hlam, hphi, p18953_1]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h18654, h18657, hc34, hc45, hlam, hphi, p18953_1]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [h18657, hc34, hc45, hlam, hphi, p18953_1]
                                    · have p18953_0 := h18953c.1
                                      have p18953_1 := h18953c.2.1
                                      have p18953_2 := h18953c.2.2.1
                                      have p18953_3 := h18953c.2.2.2
                                      linarith only [hlam, p18953_0]
                            · linarith only [h15532, h18946, hlam]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [hlam, p18938_0]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          rcases p18938_3 (m.d 0 3) (by simp) with h18981 | h18981
                          · linarith only [h15532, h18981, hlam]
                          · linarith only [h18445, h18981, hlam]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          rcases p18938_3 (m.d 0 3) (by simp) with h18984 | h18984
                          · linarith only [h15532, h18984, hlam]
                          · linarith only [h18448, h18984, hlam]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          rcases p18938_3 (m.d 0 3) (by simp) with h18987 | h18987
                          · linarith only [h15532, h18987, hlam]
                          · linarith only [h18449, h18987, hlam]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [h18445, hlam, p18938_0]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [h18646, hlam, p18938_0]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [hlam, p18938_0]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18927_1, p18938_1]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [h0, h18445, h18657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p18938_1]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [h18448, hlam, p18938_0]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [h18649, hlam, p18938_0]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [h18653, hlam, p18938_0]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [hlam, p18938_0]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [h18657, hlam, p18938_1]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [h18449, hlam, p18938_0]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [h18650, hlam, p18938_0]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [h18654, hlam, p18938_0]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [h0, h15532, h18444, h18447, h18654, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p18938_1]
                        · have p18938_0 := h18938c.1
                          have p18938_1 := h18938c.2.1
                          have p18938_2 := h18938c.2.2.1
                          have p18938_3 := h18938c.2.2.2
                          linarith only [hlam, p18938_0]
                · linarith only [h18646, h18931, hlam]
              · linarith only [h18930, hlam, p18927_0]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h15532, h18443, h18647, hlam, p18659_1, p18927_2]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h15532, h18444, h18648, hlam, p18659_1, p18927_2]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h15532, hc01, hc12, hlam, hphi, p18659_1, p18927_1]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [hlam, p18927_0]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              rcases p18927_3 (m.d 0 2) (by simp) with h19011 | h19011
              · linarith only [h0, h19011, hlam]
              · linarith only [h18445, h19011, hlam]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h0, h15532, h18444, h18647, h18651, hlam, p18659_1, p18927_2]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h0, h15532, h18444, h18648, hlam, p18659_1, p18927_2]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h18445, hlam, p18927_0]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h18646, hlam, p18927_0]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [hlam, p18927_0]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h18445, h18653, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p18659_1, p18927_1]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h0, h18445, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p18659_1, p18927_1]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h18446, hlam, p18927_0]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h18647, hlam, p18927_0]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h18653, hlam, p18927_1]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [hlam, p18927_0]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h18655, hlam, p18927_1]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h18447, hlam, p18927_0]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h18648, hlam, p18927_0]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h18654, hlam, p18927_1]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [h0, h15532, h18444, h18447, h18653, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p18927_1]
            · have p18927_0 := h18927c.1
              have p18927_1 := h18927c.2.1
              have p18927_2 := h18927c.2.2.1
              have p18927_3 := h18927c.2.2.2
              linarith only [hlam, p18927_0]
    · linarith only [h18445, h18920, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x8 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h18648 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 2) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 2) ∧ (m.d 0 4) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 4) ≤ z)))
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
  have h15532 := hg15532
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  rcases p18659_3 (m.d 0 1) (by simp) with h19032 | h19032
  · linarith only [h0, h19032, hlam]
  · linarith only [h18443, h19032, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x9 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h18648 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 2) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 2) ∧ (m.d 0 5) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 5) ≤ z)))
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
  have h15532 := hg15532
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  rcases p18659_3 (m.d 0 1) (by simp) with h19035 | h19035
  · linarith only [h0, h19035, hlam]
  · linarith only [h18444, h19035, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x10 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h18648 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 3) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 3) ∧ (m.d 0 1) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 1) ≤ z)))
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
  have h15532 := hg15532
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  rcases p18659_3 (m.d 0 1) (by simp) with h19038 | h19038
  · linarith only [h15532, h19038, hlam]
  · rcases p18659_3 (m.d 0 2) (by simp) with h19040 | h19040
    · rcases p18659_3 (m.d 0 3) (by simp) with h19041 | h19041
      · rcases p18659_3 (m.d 0 4) (by simp) with h19042 | h19042
        · linarith only [h18448, h19042, hlam]
        · rcases p18659_3 (m.d 0 5) (by simp) with h19044 | h19044
          · linarith only [h18449, h19044, hlam]
          · rcases h2bigk with h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c | h19046c
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [hlam, p19046_0]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [h0, hlam, p19046_1]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              rcases p19046_3 (m.d 0 2) (by simp) with h19049 | h19049
              · rcases p19046_3 (m.d 1 2) (by simp) with h19050 | h19050
                · rcases p19046_3 (m.d 2 3) (by simp) with h19051 | h19051
                  · linarith only [h19051, hlam, p19046_0]
                  · rcases p19046_3 (m.d 2 4) (by simp) with h19053 | h19053
                    · linarith only [h18446, h19053, hlam]
                    · rcases p19046_3 (m.d 2 5) (by simp) with h19055 | h19055
                      · linarith only [h18447, h19055, hlam]
                      · rcases h3bigk with h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c | h19057c
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [hlam, p19057_0]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h15532, hlam, p19057_1]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          rcases p19057_3 (m.d 0 3) (by simp) with h19060 | h19060
                          · rcases p19057_3 (m.d 1 3) (by simp) with h19061 | h19061
                            · rcases p19057_3 (m.d 2 3) (by simp) with h19062 | h19062
                              · linarith only [h18445, h19062, hlam]
                              · rcases p19057_3 (m.d 3 4) (by simp) with h19064 | h19064
                                · linarith only [h18448, h19064, hlam]
                                · rcases p19057_3 (m.d 3 5) (by simp) with h19066 | h19066
                                  · linarith only [h18449, h19066, hlam]
                                  · rcases h5bigk with h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c | h19068c
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [hlam, p19068_0]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h15532, h18444, h18646, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p18659_1, p19068_1]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h15532, h18444, h18646, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p18659_1, p19068_1]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h15532, h18444, h18646, h18657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p19068_1]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h18450, hlam, p19068_1]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h18444, hlam, p19068_0]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [hlam, p19068_0]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h15532, h18444, h18646, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p18659_1, p19068_1]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h15532, h18444, h18646, h18657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p19068_1]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h18651, hlam, p19068_1]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h18447, hlam, p19068_1]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h18648, hlam, p19068_1]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [hlam, p19068_0]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h0, h18447, h18657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19068_1]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h18655, hlam, p19068_1]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h18449, hlam, p19068_0]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h18650, hlam, p19068_0]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h18654, hlam, p19068_0]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [hlam, p19068_0]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h18657, hlam, p19068_1]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h18449, h18657, hc34, hc45, hlam, hphi, p19068_1]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h18650, h18657, hc34, hc45, hlam, hphi, p19068_1]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h18654, h18657, hc34, hc45, hlam, hphi, p19068_1]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [h18657, hc34, hc45, hlam, hphi, p19068_1]
                                    · have p19068_0 := h19068c.1
                                      have p19068_1 := h19068c.2.1
                                      have p19068_2 := h19068c.2.2.1
                                      have p19068_3 := h19068c.2.2.2
                                      linarith only [hlam, p19068_0]
                            · linarith only [h18646, h19061, hlam]
                          · linarith only [h18445, h19060, hlam]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h18443, h18647, h18653, hlam, p18659_1, p19057_2]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h18444, h18648, h18654, hlam, p18659_1, p19057_2]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h18444, h18646, h18647, h18651, h18653, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p19057_1]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [hlam, p19057_0]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          rcases p19057_3 (m.d 0 3) (by simp) with h19100 | h19100
                          · linarith only [h15532, h19100, hlam]
                          · linarith only [h18445, h19100, hlam]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h15532, h18444, h18647, h18651, h18653, hlam, p18659_1, p19057_2]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h15532, h18444, h18648, h18654, hlam, p18659_1, p19057_2]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h18445, hlam, p19057_0]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h18646, hlam, p19057_0]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [hlam, p19057_0]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19046_1, p19057_1]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p19046_1, p19057_1]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h18448, hlam, p19057_0]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h18649, hlam, p19057_0]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h18653, hlam, p19057_0]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [hlam, p19057_0]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h18657, hlam, p19057_1]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h18449, hlam, p19057_0]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h18650, hlam, p19057_0]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h18654, hlam, p19057_0]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [h18444, h18449, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p18659_1, p19057_1]
                        · have p19057_0 := h19057c.1
                          have p19057_1 := h19057c.2.1
                          have p19057_2 := h19057c.2.2.1
                          have p19057_3 := h19057c.2.2.2
                          linarith only [hlam, p19057_0]
                · linarith only [h18646, h19050, hlam]
              · linarith only [h19049, hlam, p19046_0]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [h18443, h18445, h18647, hlam, p18659_1, p19046_2]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [h18444, h18445, h18648, hlam, p18659_1, p19046_2]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [h18445, hc01, hc12, hlam, hphi, p18659_1, p19046_1]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [hlam, p19046_0]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              rcases p19046_3 (m.d 0 2) (by simp) with h19126 | h19126
              · linarith only [h0, h19126, hlam]
              · linarith only [h18445, h19126, hlam]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [h0, h18444, h18445, h18647, h18651, hlam, p18659_1, p19046_2]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [h0, h18444, h18445, h18648, hlam, p18659_1, p19046_2]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [h18445, hlam, p19046_0]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [h18646, hlam, p19046_0]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [hlam, p19046_0]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              rcases p19046_3 (m.d 0 2) (by simp) with h19134 | h19134
              · rcases p19046_3 (m.d 1 2) (by simp) with h19135 | h19135
                · rcases p19046_3 (m.d 2 3) (by simp) with h19136 | h19136
                  · rcases p19046_3 (m.d 2 4) (by simp) with h19137 | h19137
                    · linarith only [h18653, h19137, hlam]
                    · rcases p19046_3 (m.d 2 5) (by simp) with h19139 | h19139
                      · linarith only [h18654, h19139, hlam]
                      · linarith only [h18655, h19139, hlam]
                  · linarith only [h18653, h19136, hlam]
                · linarith only [h18647, h19135, hlam]
              · linarith only [h18446, h19134, hlam]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              rcases p19046_3 (m.d 0 2) (by simp) with h19145 | h19145
              · rcases p19046_3 (m.d 1 2) (by simp) with h19146 | h19146
                · rcases p19046_3 (m.d 2 3) (by simp) with h19147 | h19147
                  · rcases p19046_3 (m.d 2 4) (by simp) with h19148 | h19148
                    · linarith only [h18653, h19148, hlam]
                    · rcases p19046_3 (m.d 2 5) (by simp) with h19150 | h19150
                      · linarith only [h18654, h19150, hlam]
                      · rcases h3bigk with h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c | h19152c
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [hlam, p19152_0]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h15532, hlam, p19152_1]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h18445, hc02, hc25, hlam, hphi, ht0b, ht5b, p19046_1, p19152_1]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h18444, h18647, h18651, h18653, hlam, p18659_1, p19152_2]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h18444, h18648, h18654, hlam, p18659_1, p19152_2]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h18444, h18646, h18647, h18651, h18653, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p19152_1]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [hlam, p19152_0]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h18646, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p19046_1, p19152_1]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h15532, h18444, h18647, h18651, h18653, hlam, p18659_1, p19152_2]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h15532, h18444, h18648, h18654, hlam, p18659_1, p19152_2]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h18445, hlam, p19152_0]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h18646, hlam, p19152_0]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [hlam, p19152_0]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          rcases p19152_3 (m.d 0 3) (by simp) with h19166 | h19166
                          · rcases p19152_3 (m.d 1 3) (by simp) with h19167 | h19167
                            · rcases p19152_3 (m.d 2 3) (by simp) with h19168 | h19168
                              · rcases p19152_3 (m.d 3 4) (by simp) with h19169 | h19169
                                · linarith only [h19169, hlam, p19152_0]
                                · rcases p19152_3 (m.d 3 5) (by simp) with h19171 | h19171
                                  · linarith only [h18654, h19171, hlam]
                                  · linarith only [h18657, h19171, hlam]
                              · linarith only [h19168, hlam, p19152_0]
                            · linarith only [h18649, h19167, hlam]
                          · linarith only [h18448, h19166, hlam]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          rcases p19152_3 (m.d 0 3) (by simp) with h19177 | h19177
                          · rcases p19152_3 (m.d 1 3) (by simp) with h19178 | h19178
                            · rcases p19152_3 (m.d 2 3) (by simp) with h19179 | h19179
                              · rcases p19152_3 (m.d 3 4) (by simp) with h19180 | h19180
                                · linarith only [h18653, h19180, hlam]
                                · rcases p19152_3 (m.d 3 5) (by simp) with h19182 | h19182
                                  · linarith only [h19182, hlam, p19152_0]
                                  · rcases h5bigk with h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c | h19184c
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [hlam, p19184_0]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h18444, h18445, h18647, h18651, h18653, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p18659_1, p19184_1]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h0, h18444, h18445, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p18659_1, p19184_1]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h0, h18444, h18445, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p18659_1, p19184_1]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h18450, hlam, p19184_1]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h18444, hlam, p19184_0]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [hlam, p19184_0]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h0, h18444, h18445, h18654, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p18659_1, p19184_1]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h0, h18444, h18445, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p18659_1, p19184_1]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h18651, hlam, p19184_1]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h18447, hlam, p19184_1]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h18648, hlam, p19184_1]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [hlam, p19184_0]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p19046_1, p19184_1]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h18655, hlam, p19184_1]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h18449, hlam, p19184_0]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h18650, hlam, p19184_0]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h18654, hlam, p19184_0]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [hlam, p19184_0]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h18657, hlam, p19184_1]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h18443, h18450, h18647, h18653, hc34, hc45, hlam, hphi, p19184_1]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h18647, h18651, h18653, hc34, hc45, hlam, hphi, p19184_1]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h18653, h18655, hc34, hc45, hlam, hphi, p19184_1]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [h18657, hc34, hc45, hlam, hphi, p19184_1]
                                    · have p19184_0 := h19184c.1
                                      have p19184_1 := h19184c.2.1
                                      have p19184_2 := h19184c.2.2.1
                                      have p19184_3 := h19184c.2.2.2
                                      linarith only [hlam, p19184_0]
                              · linarith only [h19179, hlam, p19152_0]
                            · linarith only [h18650, h19178, hlam]
                          · linarith only [h18449, h19177, hlam]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h18448, hlam, p19152_0]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h18649, hlam, p19152_0]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h18653, hlam, p19152_0]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [hlam, p19152_0]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h18657, hlam, p19152_1]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h18449, hlam, p19152_0]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h18650, hlam, p19152_0]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h18654, hlam, p19152_0]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [h0, h18444, h18445, h18449, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p19152_1]
                        · have p19152_0 := h19152c.1
                          have p19152_1 := h19152c.2.1
                          have p19152_2 := h19152c.2.2.1
                          have p19152_3 := h19152c.2.2.2
                          linarith only [hlam, p19152_0]
                  · linarith only [h18654, h19147, hlam]
                · linarith only [h18648, h19146, hlam]
              · linarith only [h18447, h19145, hlam]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [h18446, hlam, p19046_0]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [h18647, hlam, p19046_0]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [h18653, hlam, p19046_1]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [hlam, p19046_0]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [h18655, hlam, p19046_1]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [h18447, hlam, p19046_0]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [h18648, hlam, p19046_0]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [h18654, hlam, p19046_1]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [h0, h18444, h18445, h18447, h18653, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18659_1, p19046_1]
            · have p19046_0 := h19046c.1
              have p19046_1 := h19046c.2.1
              have p19046_2 := h19046c.2.2.1
              have p19046_3 := h19046c.2.2.2
              linarith only [hlam, p19046_0]
      · linarith only [h15532, h19041, hlam]
    · linarith only [h0, h19040, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x11 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18445 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18446 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18447 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18448 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h18449 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h18450 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h18646 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h18647 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h18648 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h18649 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h18650 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h18651 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h18653 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h18654 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h18655 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h18657 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h18659c : ((m.d 0 3) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 3) ∧ (m.d 0 2) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 2) ≤ z)))
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
  have h15532 := hg15532
  have p18659_0 := h18659c.1
  have p18659_1 := h18659c.2.1
  have p18659_2 := h18659c.2.2.1
  have p18659_3 := h18659c.2.2.2
  linarith only [h18445, hlam, p18659_1]

end R2N4
