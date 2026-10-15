import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_13S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7524000 in
set_option maxHeartbeats 7524000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7870 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8661 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8662 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  have h6923 := hg6923
  have h7870 := hg7870
  rcases m.htr 0 2 5 (by decide) (by decide) with h10726 | h10726
  · rcases m.htr 0 3 4 (by decide) (by decide) with h10727 | h10727
    · linarith only [h10727, h8661, h8662, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h10729 | h10729
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10730 | h10730
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10731 | h10731
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10732 | h10732
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10733 | h10733
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10734 | h10734
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10735 | h10735
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10736 | h10736
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10737 | h10737
                      · linarith only [h10727, h10732, h10737, h8661, h8662, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10739 | h10739
                        · linarith only [h10731, h10734, h10737, h10739, h8661, h8662, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h10729, h10731, h10734, h10737, h10739, h8661, h8662, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h10732, h10736, h8661, h8662, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h10727, h10729, h10734, h10735, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10744 | h10744
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10745 | h10745
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10746 | h10746
                      · linarith only [h10734, h10746, h5135, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10748 | h10748
                        · linarith only [h10732, h10748, h8661, h8662, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h10729, h10732, h10748, h8661, h8662, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h10726, h10730, h10732, h10745, h8662, hc04, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h10729, h10744, h5135, hlam]
              · linarith only [h10732, h10733, h8661, h8662, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10754 | h10754
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10755 | h10755
                · linarith only [h10727, h10729, h10731, h10732, h10755, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10757 | h10757
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10758 | h10758
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10759 | h10759
                      · linarith only [h0, h10732, h10755, h10759, h6923, h8661, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10761 | h10761
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10762 | h10762
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10763 | h10763
                            · rcases h2bigk with h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c | h10764c
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [hlam, p10764_0]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h0, hlam, p10764_0]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h10761, h10763, hc02, hc45, hlam, hphi, ht0b, ht5b, p10764_1]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h8662, hlam, p10764_0]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h10759, h8662, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10764_1]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p10764_1]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [hlam, p10764_0]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h10761, h10763, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10764_1]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h10732, hlam, p10764_0]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h10732, h10759, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10764_1]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h8661, hlam, p10764_0]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h10731, hlam, p10764_0]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [hlam, p10764_0]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h10759, hlam, p10764_1]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h8661, hc02, hc25, hlam, hphi, ht0b, ht5b, p10764_1]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h10759, hc02, hc34, hlam, hphi, ht23, p10764_1]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h10759, hc12, hc34, hlam, hphi, ht23, p10764_1]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h10759, hc23, hc34, hlam, hphi, p10764_1]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [hlam, p10764_0]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                rcases p10764_3 (m.d 0 2) (by simp) with h10784 | h10784
                                · linarith only [h10784, h8662, hlam]
                                · linarith only [h10726, h10784, hlam]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h10726, hlam, p10764_0]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h10754, hlam, p10764_0]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h10761, hlam, p10764_0]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [h10762, hlam, p10764_1]
                              · have p10764_0 := h10764c.1
                                have p10764_1 := h10764c.2.1
                                have p10764_2 := h10764c.2.2.1
                                have p10764_3 := h10764c.2.2.2
                                linarith only [hlam, p10764_0]
                            · linarith only [h10759, h10763, h8661, h8662, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h10729, h10730, h10732, h10761, h10762, h8661, hc03, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h10729, h10732, h10759, h10761, h8661, hc23, hc34, hlam, hphi]
                    · linarith only [h10730, h10758, h6923, hlam]
                  · linarith only [h0, h10729, h10732, h10757, h5135, h8661, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h10726, h10754, hlam]
          · linarith only [h0, h10731, h8661, hlam]
        · linarith only [h10729, h10730, h8661, h8662, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10800 | h10800
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10801 | h10801
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10802 | h10802
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10803 | h10803
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10804 | h10804
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10805 | h10805
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10806 | h10806
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10807 | h10807
                      · linarith only [h10727, h10802, h10807, h8661, h8662, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10809 | h10809
                        · linarith only [h10729, h10801, h10804, h10807, h10809, h5135, h8661, h8662, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10811 | h10811
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10812 | h10812
                            · rcases h2bigk with h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c | h10813c
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [hlam, p10813_0]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h0, hlam, p10813_0]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h10801, h10804, h10807, h8662, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10813_1]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h8662, hlam, p10813_0]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h10801, h10804, h10807, h8662, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p10813_1]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p10813_1]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [hlam, p10813_0]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                rcases p10813_3 (m.d 0 2) (by simp) with h10821 | h10821
                                · linarith only [h0, h10821, hlam]
                                · linarith only [h10821, h8661, hlam]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h10726, h10809, h8662, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10813_1]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                rcases p10813_3 (m.d 0 2) (by simp) with h10825 | h10825
                                · linarith only [h0, h10825, hlam]
                                · linarith only [h10726, h10825, hlam]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h8661, hlam, p10813_0]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h10801, hlam, p10813_0]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [hlam, p10813_0]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h10807, hlam, p10813_1]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h10809, hlam, p10813_1]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h10726, h10809, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p10813_1]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h10802, hlam, p10813_0]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h10801, h10804, h10807, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10813_1]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [hlam, p10813_0]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h10801, h10804, h10807, h10809, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10813_1]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h10726, hlam, p10813_0]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h10803, hlam, p10813_0]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h10726, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10813_1]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [h10811, hlam, p10813_1]
                              · have p10813_0 := h10813c.1
                                have p10813_1 := h10813c.2.1
                                have p10813_2 := h10813c.2.2.1
                                have p10813_3 := h10813c.2.2.2
                                linarith only [hlam, p10813_0]
                            · linarith only [h10807, h10812, h8661, h8662, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h10726, h10809, h10811, h8662, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h10726, h10800, h10806, h6923, h8662, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h10727, h10804, h10805, h8661, h8662, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10847 | h10847
                  · linarith only [h10729, h10804, h10847, h5135, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10849 | h10849
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10850 | h10850
                      · linarith only [h10802, h10804, h10850, h8661, h8662, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10852 | h10852
                        · linarith only [h10802, h10847, h10852, h5135, h8661, h8662, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10854 | h10854
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10855 | h10855
                            · rcases h2bigk with h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c | h10856c
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [hlam, p10856_0]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h0, hlam, p10856_0]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h10802, h8662, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10856_1]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h8662, hlam, p10856_0]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h10802, h8662, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p10856_1]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p10856_1]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [hlam, p10856_0]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                rcases p10856_3 (m.d 0 2) (by simp) with h10864 | h10864
                                · linarith only [h0, h10864, hlam]
                                · linarith only [h10864, h8661, hlam]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h10726, h10852, h8662, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10856_1]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                rcases p10856_3 (m.d 0 2) (by simp) with h10868 | h10868
                                · linarith only [h0, h10868, hlam]
                                · linarith only [h10726, h10868, hlam]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h8661, hlam, p10856_0]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h10801, hlam, p10856_0]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [hlam, p10856_0]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h10850, hlam, p10856_1]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h10852, hlam, p10856_1]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h10726, h10852, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p10856_1]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h10802, hlam, p10856_0]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h10802, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10856_1]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [hlam, p10856_0]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h10802, h10852, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10856_1]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h10726, hlam, p10856_0]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h10803, hlam, p10856_0]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h10726, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10856_1]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [h10854, hlam, p10856_1]
                              · have p10856_0 := h10856c.1
                                have p10856_1 := h10856c.2.1
                                have p10856_2 := h10856c.2.2.1
                                have p10856_3 := h10856c.2.2.2
                                linarith only [hlam, p10856_0]
                            · linarith only [h10800, h10804, h10855, h6923, hlam]
                          · linarith only [h10726, h10800, h10854, h8662, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h10726, h10800, h10849, h6923, h8662, hlam]
              · linarith only [h10726, h10803, h8662, hc12, hc24, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10890 | h10890
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10891 | h10891
                · linarith only [h10727, h10801, h10802, h10891, h5135, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10893 | h10893
                  · linarith only [h10729, h10891, h10893, h5135, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10895 | h10895
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10896 | h10896
                      · linarith only [h10802, h10890, h10891, h10893, h10896, h5135, h6923, h8661, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10898 | h10898
                        · linarith only [h0, h10802, h10893, h10896, h10898, h8661, hc13, hc34, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10900 | h10900
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10901 | h10901
                            · rcases h2bigk with h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c | h10902c
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [hlam, p10902_0]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h0, hlam, p10902_0]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h0, h10802, h10896, hc23, hc34, hlam, hphi, p10902_1]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h8662, hlam, p10902_0]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h0, h10802, h10896, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10902_1]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h10802, h10896, hc02, hc34, hlam, hphi, ht23, p10902_1]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [hlam, p10902_0]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h10802, h10896, hc23, hc34, hlam, hphi, p10902_1]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h10802, hlam, p10902_0]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h10802, h10896, h10900, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10902_1]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h8661, hlam, p10902_0]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h10801, hlam, p10902_0]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [hlam, p10902_0]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h10896, hlam, p10902_1]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h10898, hlam, p10902_1]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h10896, h8661, hc23, hc34, hlam, hphi, p10902_1]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h10896, hc12, hc34, hlam, hphi, ht23, p10902_1]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h10896, hc23, hc34, hlam, hphi, p10902_1]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [hlam, p10902_0]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h10896, h10898, hc23, hc34, hlam, hphi, p10902_1]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h10726, hlam, p10902_0]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h10890, hlam, p10902_0]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h10726, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10902_1]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [h10900, hlam, p10902_1]
                              · have p10902_0 := h10902c.1
                                have p10902_1 := h10902c.2.1
                                have p10902_2 := h10902c.2.2.1
                                have p10902_3 := h10902c.2.2.2
                                linarith only [hlam, p10902_0]
                            · linarith only [h0, h10802, h10896, h10901, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h10802, h10890, h10893, h10900, h5135, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h10726, h10800, h10802, h10895, h6923, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h10726, h10890, hlam]
          · linarith only [h0, h10801, h8661, hlam]
        · linarith only [h10726, h10800, h8662, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h10934 | h10934
    · linarith only [h10934, h8661, h8662, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h10936 | h10936
      · linarith only [h10726, h10936, h8661, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10938 | h10938
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10939 | h10939
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10940 | h10940
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10941 | h10941
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10942 | h10942
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10943 | h10943
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10944 | h10944
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10945 | h10945
                      · linarith only [h10934, h10940, h10945, h8661, h8662, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10947 | h10947
                        · linarith only [h10936, h10939, h10942, h10945, h10947, h5135, h8661, h8662, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10949 | h10949
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10950 | h10950
                            · rcases h2bigk with h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c | h10951c
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [hlam, p10951_0]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h0, hlam, p10951_0]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h10726, h10939, h10942, h10945, h10949, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10951_1]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h8662, hlam, p10951_0]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h10726, hlam, p10951_0]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p10951_1]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [hlam, p10951_0]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                rcases p10951_3 (m.d 0 2) (by simp) with h10959 | h10959
                                · linarith only [h0, h10959, hlam]
                                · linarith only [h10959, h8661, hlam]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h8661, h8662, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10951_1]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h10726, h8661, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10951_1]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h8661, hlam, p10951_0]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h10939, hlam, p10951_0]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [hlam, p10951_0]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h10945, hlam, p10951_1]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h10947, hlam, p10951_1]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h10940, h8661, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10951_1]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h10940, hlam, p10951_0]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h10939, h10942, h10945, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10951_1]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [hlam, p10951_0]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h10726, h10939, h10942, h10945, h8661, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10951_1]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h10943, h10947, h8661, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10951_1]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h10941, hlam, p10951_0]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h10939, h10943, h10947, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10951_1]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [h10949, hlam, p10951_1]
                              · have p10951_0 := h10951c.1
                                have p10951_1 := h10951c.2.1
                                have p10951_2 := h10951c.2.2.1
                                have p10951_3 := h10951c.2.2.2
                                linarith only [hlam, p10951_0]
                            · linarith only [h10945, h10950, h8661, h8662, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h10938, h10949, h8661, h8662, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h10936, h10938, h10939, h10943, h10944, h6923, hc01, hc12, hlam, hphi]
                  · linarith only [h10934, h10942, h10943, h8661, h8662, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10983 | h10983
                  · linarith only [h10936, h10942, h10983, h5135, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10985 | h10985
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10986 | h10986
                      · linarith only [h10940, h10942, h10986, h8661, h8662, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10988 | h10988
                        · linarith only [h10726, h10941, h10983, h10988, h8661, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10990 | h10990
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10991 | h10991
                            · rcases h2bigk with h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [hlam, p10992_0]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h0, hlam, p10992_0]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h10726, h10940, h10990, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10992_1]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h8662, hlam, p10992_0]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h10726, hlam, p10992_0]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p10992_1]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [hlam, p10992_0]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                rcases p10992_3 (m.d 0 2) (by simp) with h11000 | h11000
                                · linarith only [h0, h11000, hlam]
                                · linarith only [h11000, h8661, hlam]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h8661, h8662, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10992_1]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h10726, h8661, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10992_1]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h8661, hlam, p10992_0]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h10939, hlam, p10992_0]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [hlam, p10992_0]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h10986, hlam, p10992_1]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h10988, hlam, p10992_1]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h10940, h8661, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10992_1]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h10940, hlam, p10992_0]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h10940, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10992_1]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [hlam, p10992_0]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h10726, h10940, h8661, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10992_1]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h10941, h8661, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10992_1]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h10941, hlam, p10992_0]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h10941, h10983, hc23, hc35, hlam, hphi, p10992_1]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [h10990, hlam, p10992_1]
                              · have p10992_0 := h10992c.1
                                have p10992_1 := h10992c.2.1
                                have p10992_2 := h10992c.2.2.1
                                have p10992_3 := h10992c.2.2.2
                                linarith only [hlam, p10992_0]
                            · linarith only [h10938, h10942, h10991, h6923, hlam]
                          · linarith only [h10938, h10990, h8662, hlam]
                    · linarith only [h10938, h10985, h6923, h8662, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h10940, h10941, h8661, h8662, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11024 | h11024
              · linarith only [h10726, h10940, h11024, h8661, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h11026 | h11026
                · linarith only [h10934, h10939, h10940, h11026, h5135, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11028 | h11028
                  · linarith only [h10936, h11026, h11028, h5135, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11030 | h11030
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11031 | h11031
                      · linarith only [h0, h10940, h11026, h11031, h8661, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11033 | h11033
                        · linarith only [h11028, h11033, h5135, h8661, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11035 | h11035
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h11036 | h11036
                            · rcases h2bigk with h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [hlam, p11037_0]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h0, hlam, p11037_0]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h0, h11024, h11031, h11035, hc23, hc34, hlam, hphi, p11037_1]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h8662, hlam, p11037_0]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h10726, hlam, p11037_0]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h11024, h11031, h11035, hc02, hc34, hlam, hphi, ht23, p11037_1]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [hlam, p11037_0]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h11024, h11031, h11035, hc23, hc34, hlam, hphi, p11037_1]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h10940, hlam, p11037_0]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h11024, hlam, p11037_0]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h8661, hlam, p11037_0]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h10939, hlam, p11037_0]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [hlam, p11037_0]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h11031, hlam, p11037_1]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h11033, hlam, p11037_1]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h11031, h8661, hc23, hc34, hlam, hphi, p11037_1]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h11031, hc12, hc34, hlam, hphi, ht23, p11037_1]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h11031, hc23, hc34, hlam, hphi, p11037_1]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [hlam, p11037_0]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h10726, h11031, h8661, hc23, hc34, hlam, hphi, p11037_1]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h8661, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11037_1]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h10939, h11033, h5135, hc01, hc35, hlam, hphi, ht12, ht23, p11037_1]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h11033, hc23, hc35, hlam, hphi, p11037_1]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [h11035, hlam, p11037_1]
                              · have p11037_0 := h11037c.1
                                have p11037_1 := h11037c.2.1
                                have p11037_2 := h11037c.2.2.1
                                have p11037_3 := h11037c.2.2.2
                                linarith only [hlam, p11037_0]
                            · linarith only [h10938, h10940, h11031, h11036, h6923, hlam]
                          · linarith only [h10938, h10940, h11035, h6923, hlam]
                    · linarith only [h10938, h11030, h6923, hlam]
          · linarith only [h0, h10939, h8661, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h11067 | h11067
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11068 | h11068
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11069 | h11069
              · rcases m.htr 1 3 4 (by decide) (by decide) with h11070 | h11070
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11071 | h11071
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11072 | h11072
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11073 | h11073
                      · linarith only [h10934, h10938, h11067, h11070, h11072, h11073, h5135, h8661, h8662, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11075 | h11075
                        · linarith only [h10938, h11067, h11070, h11072, h11075, h8661, h8662, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11077 | h11077
                          · linarith only [h10938, h11073, h11077, h8661, h8662, hc23, hc34, hlam, hphi]
                          · linarith only [h11067, h11070, h11072, h11077, h8661, h8662, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h11068, h11072, h8661, h8662, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h10934, h11070, h11071, h5135, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11082 | h11082
                  · linarith only [h10936, h11070, h11082, h5135, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11084 | h11084
                    · linarith only [h10938, h11070, h11084, h8661, h8662, hc23, hc34, hlam, hphi]
                    · linarith only [h11068, h11084, h8661, h8662, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h11068, h11069, h8661, h8662, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11088 | h11088
              · linarith only [h10726, h11068, h11088, h8661, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h11090 | h11090
                · linarith only [h10934, h11067, h11068, h11090, h5135, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h11092 | h11092
                  · linarith only [h10936, h11090, h11092, h5135, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h11094 | h11094
                    · linarith only [h10938, h11090, h11094, h8661, h8662, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11096 | h11096
                      · linarith only [h0, h11068, h11094, h11096, h8661, hc34, hc45, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11098 | h11098
                        · linarith only [h11092, h11098, h5135, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h11100 | h11100
                          · linarith only [h0, h11068, h11094, h11096, h11100, h8661, hc23, hc34, hlam, hphi]
                          · linarith only [h11100, h8661, h8662, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h11067, h8661, h8662, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 7524000 in
set_option maxHeartbeats 7524000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s8_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7870 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8661 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  have h6923 := hg6923
  have h7870 := hg7870
  rcases m.htr 0 2 4 (by decide) (by decide) with h8662 | h8662
  · exact r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0 m hb2 hb3 hb5 hg0 hg5135 hg6923 hg7870 h8661 h8662
  · exact r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x1 m hb2 hb3 hb5 hg0 hg5135 hg6923 hg7870 h8661 h8662

end R2N4
