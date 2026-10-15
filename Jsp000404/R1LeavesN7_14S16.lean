import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_14S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10612000 in
set_option maxHeartbeats 10612000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s5 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  rcases m.htr 0 1 4 (by decide) (by decide) with h6681 | h6681
  · rcases m.htr 0 1 5 (by decide) (by decide) with h6682 | h6682
    · rcases m.htr 0 2 3 (by decide) (by decide) with h6683 | h6683
      · rcases m.htr 0 2 4 (by decide) (by decide) with h6684 | h6684
        · rcases m.htr 0 2 5 (by decide) (by decide) with h6685 | h6685
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6686 | h6686
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6687 | h6687
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6688 | h6688
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6689 | h6689
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6690 | h6690
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6691 | h6691
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6692 | h6692
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6693 | h6693
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6694 | h6694
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6695 | h6695
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6696 | h6696
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6697 | h6697
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6698 | h6698
                                    · linarith only [h6683, h6695, h6698, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h4610, h6681, h6683, h6694, h6698, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · linarith only [h4610, h6681, h6683, h6694, h6697, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h4610, h6681, h6683, h6693, h6694, h6695, h6696, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6703 | h6703
                                · linarith only [h6683, h6686, h6695, h6703, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6705 | h6705
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6706 | h6706
                                    · rcases h0bigk with h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c | h6707c
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [hlam, p6707_0]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h0, hlam, p6707_1]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h4610, hlam, p6707_0]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h4610, h6681, h6683, h6693, h6694, h6703, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6707_1, u0elo1]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h4610, h6682, h6683, h6693, h6703, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6707_1, u0elo1]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h6681, h6693, h6694, h6703, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6707_1, u0elo1]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [hlam, p6707_0]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h4610, h6681, h6693, h6694, h6703, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6707_1, u0elo1]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h6681, h6693, h6694, h6703, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6707_1, u0elo1]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h6682, h6693, h6703, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6707_1, u0elo1]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h6681, h6693, h6694, h6703, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6707_1, u0elo2]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h6683, hlam, p6707_1]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [hlam, p6707_0]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h6681, h6683, h6693, h6694, h6703, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6707_1, u0elo1]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h6682, h6683, h6693, h6703, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6707_1, u0elo1]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h6681, hlam, p6707_0]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h6684, hlam, p6707_0]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h6686, hlam, p6707_0]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [hlam, p6707_0]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h6682, h6693, h6703, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6707_1, u0elo3]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h6682, hlam, p6707_0]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h6685, hlam, p6707_1]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h6687, hlam, p6707_0]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [h6688, hlam, p6707_1]
                                      · have p6707_0 := h6707c.1
                                        have p6707_1 := h6707c.2.1
                                        have p6707_2 := h6707c.2.2.1
                                        have p6707_3 := h6707c.2.2.2
                                        linarith only [hlam, p6707_0]
                                    · linarith only [h6681, h6694, h6706, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · linarith only [h4610, h6681, h6683, h6694, h6705, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6735 | h6735
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6736 | h6736
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6737 | h6737
                                  · linarith only [h6684, h6694, h6737, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6739 | h6739
                                    · linarith only [h6690, h6694, h6735, h6739, hlam]
                                    · rcases h0bigk with h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c | h6741c
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [hlam, p6741_0]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h0, hlam, p6741_1]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h4610, hlam, p6741_0]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h4610, h6683, h6688, h6690, h6694, h6735, hc34, hlam, hphi, ht0b, ht45, ht5b, p6741_1, u0elo1]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h4610, h6683, h6688, h6690, h6694, h6735, hc34, hlam, hphi, ht0b, ht45, ht5b, p6741_1, u0elo1]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h6681, h6690, h6735, hc34, hlam, hphi, ht0b, ht45, ht5b, p6741_1, u0elo1]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [hlam, p6741_0]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h4610, h6681, h6690, h6735, hc34, hlam, hphi, ht0b, ht45, ht5b, p6741_1, u0elo1]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h6688, h6690, h6694, h6735, hc34, hlam, hphi, ht0b, ht45, ht5b, p6741_1, u0elo1]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h6688, h6690, h6694, h6735, hc34, hlam, hphi, ht0b, ht45, ht5b, p6741_1, u0elo1]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h6681, h6688, h6690, h6694, h6735, hc34, hlam, hphi, ht0b, ht45, ht5b, p6741_1, u0elo2]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h6683, hlam, p6741_1]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [hlam, p6741_0]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h6683, h6688, h6690, h6694, h6735, hc34, hlam, hphi, ht0b, ht45, ht5b, p6741_1, u0elo1]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h6683, h6688, h6690, h6694, h6735, hc34, hlam, hphi, ht0b, ht45, ht5b, p6741_1, u0elo1]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h6681, hlam, p6741_0]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h6684, hlam, p6741_0]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h6686, hlam, p6741_0]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [hlam, p6741_0]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h6681, h6688, h6690, h6694, h6735, hc34, hlam, hphi, ht0b, ht45, ht5b, p6741_1, u0elo0]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h6682, hlam, p6741_0]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h6685, hlam, p6741_1]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h6687, hlam, p6741_0]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [h6688, hlam, p6741_1]
                                      · have p6741_0 := h6741c.1
                                        have p6741_1 := h6741c.2.1
                                        have p6741_2 := h6741c.2.2.1
                                        have p6741_3 := h6741c.2.2.2
                                        linarith only [hlam, p6741_0]
                                · linarith only [h6683, h6687, h6735, h6736, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h4610, h6681, h6688, h6689, h6692, h6694, h6735, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h4610, h6687, h6693, hlam]
                        · linarith only [h4610, h6683, h6686, h6692, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h6685, h6691, hlam]
                    · linarith only [h0, h6684, h6690, hlam]
                  · linarith only [h0, h6683, h6689, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6774 | h6774
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6775 | h6775
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6776 | h6776
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6777 | h6777
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6778 | h6778
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6779 | h6779
                            · linarith only [h6681, h6688, h6779, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6781 | h6781
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6782 | h6782
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6783 | h6783
                                  · linarith only [h6681, h6688, h6775, h6783, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6785 | h6785
                                    · linarith only [h6683, h6686, h6688, h6785, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                    · rcases h0bigk with h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [hlam, p6787_0]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [h0, hlam, p6787_1]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [h4610, hlam, p6787_0]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        rcases p6787_3 (m.d 0 1) (by simp) with h6791 | h6791
                                        · rcases p6787_3 (m.d 0 2) (by simp) with h6792 | h6792
                                          · rcases p6787_3 (m.d 0 3) (by simp) with h6793 | h6793
                                            · rcases p6787_3 (m.d 0 4) (by simp) with h6794 | h6794
                                              · linarith only [h6681, h6794, hlam]
                                              · rcases p6787_3 (m.d 0 5) (by simp) with h6796 | h6796
                                                · linarith only [h6682, h6796, hlam]
                                                · linarith only [h6688, h6796, hlam]
                                            · linarith only [h6686, h6793, hlam]
                                          · linarith only [h6684, h6792, hlam]
                                        · linarith only [h6681, h6791, hlam]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        rcases p6787_3 (m.d 0 1) (by simp) with h6802 | h6802
                                        · rcases p6787_3 (m.d 0 2) (by simp) with h6803 | h6803
                                          · rcases p6787_3 (m.d 0 3) (by simp) with h6804 | h6804
                                            · rcases p6787_3 (m.d 0 4) (by simp) with h6805 | h6805
                                              · linarith only [h6681, h6805, hlam]
                                              · rcases p6787_3 (m.d 0 5) (by simp) with h6807 | h6807
                                                · linarith only [h6682, h6807, hlam]
                                                · rcases h2bigk with h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [hlam, p6809_0]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [h0, hlam, p6809_1]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [h6781, hc34, hlam, hphi, ht0b, ht45, ht5b, p6809_1, u0elo1]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    rcases p6809_3 (m.d 0 2) (by simp) with h6813 | h6813
                                                    · rcases p6809_3 (m.d 1 2) (by simp) with h6814 | h6814
                                                      · rcases p6809_3 (m.d 2 3) (by simp) with h6815 | h6815
                                                        · linarith only [h6683, h6815, hlam]
                                                        · linarith only [h6781, h6815, hlam]
                                                      · linarith only [h6775, h6814, hlam]
                                                    · linarith only [h6813, hlam, p6809_0]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    rcases p6809_3 (m.d 0 2) (by simp) with h6820 | h6820
                                                    · rcases p6809_3 (m.d 1 2) (by simp) with h6821 | h6821
                                                      · rcases p6809_3 (m.d 2 3) (by simp) with h6822 | h6822
                                                        · linarith only [h6683, h6822, hlam]
                                                        · linarith only [h6782, h6822, hlam]
                                                      · linarith only [h6776, h6821, hlam]
                                                    · linarith only [h6820, hlam, p6809_0]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [h0, h6681, h6688, h6775, h6781, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6787_1, p6809_1]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [hlam, p6809_0]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    rcases p6809_3 (m.d 0 2) (by simp) with h6829 | h6829
                                                    · linarith only [h0, h6829, hlam]
                                                    · linarith only [h6683, h6829, hlam]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [h0, h6681, h6688, h6775, hlam, p6787_1, p6809_2]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [h4610, h6685, h6774, hlam, p6787_1, p6809_2]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [h6683, hlam, p6809_0]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [h6774, hlam, p6809_0]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [hlam, p6809_0]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [h6683, h6781, hc34, hlam, hphi, ht0b, ht45, ht5b, p6809_1, u0elo1]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [h6683, hc25, hlam, hphi, ht0b, ht5b, p6809_1, u0elo1]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [h6684, hlam, p6809_0]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [h6775, hlam, p6809_0]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [h6781, hlam, p6809_1]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [hlam, p6809_0]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [h6783, hlam, p6809_1]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [h6685, hlam, p6809_0]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [h6776, hlam, p6809_0]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [h6782, hlam, p6809_1]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [h6685, h6781, hc34, hlam, hphi, ht0b, ht45, ht5b, p6809_1, u0elo1]
                                                  · have p6809_0 := h6809c.1
                                                    have p6809_1 := h6809c.2.1
                                                    have p6809_2 := h6809c.2.2.1
                                                    have p6809_3 := h6809c.2.2.2
                                                    linarith only [hlam, p6809_0]
                                            · linarith only [h6687, h6804, hlam]
                                          · linarith only [h6685, h6803, hlam]
                                        · linarith only [h6682, h6802, hlam]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [h6681, h6775, h6781, hc34, hlam, hphi, ht0b, ht45, ht5b, p6787_1, u0elo1]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [hlam, p6787_0]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [h4610, h6682, h6775, h6779, h6781, hc34, hlam, hphi, ht0b, ht45, ht5b, p6787_1, u0elo1]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        rcases p6787_3 (m.d 0 1) (by simp) with h6855 | h6855
                                        · linarith only [h0, h6855, hlam]
                                        · linarith only [h6681, h6855, hlam]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        rcases p6787_3 (m.d 0 1) (by simp) with h6858 | h6858
                                        · linarith only [h0, h6858, hlam]
                                        · linarith only [h6682, h6858, hlam]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [h6682, h6775, h6779, h6781, hc34, hlam, hphi, ht0b, ht45, ht5b, p6787_1, u0elo2]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [h6683, hlam, p6787_1]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [hlam, p6787_0]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        rcases p6787_3 (m.d 0 1) (by simp) with h6864 | h6864
                                        · linarith only [h4610, h6864, hlam]
                                        · linarith only [h6681, h6864, hlam]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        rcases p6787_3 (m.d 0 1) (by simp) with h6867 | h6867
                                        · linarith only [h4610, h6867, hlam]
                                        · linarith only [h6682, h6867, hlam]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [h6681, hlam, p6787_0]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [h6684, hlam, p6787_0]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [h6686, hlam, p6787_0]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [hlam, p6787_0]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [h6688, hlam, p6787_0]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [h6682, hlam, p6787_0]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [h6685, hlam, p6787_1]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [h6687, hlam, p6787_0]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        rcases p6787_3 (m.d 0 1) (by simp) with h6878 | h6878
                                        · rcases p6787_3 (m.d 0 2) (by simp) with h6879 | h6879
                                          · rcases p6787_3 (m.d 0 3) (by simp) with h6880 | h6880
                                            · rcases p6787_3 (m.d 0 4) (by simp) with h6881 | h6881
                                              · linarith only [h6688, h6881, hlam]
                                              · rcases p6787_3 (m.d 0 5) (by simp) with h6883 | h6883
                                                · rcases h2bigk with h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c | h6884c
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [hlam, p6884_0]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [h0, hlam, p6884_1]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [h6781, hc34, hlam, hphi, ht0b, ht45, ht5b, p6884_1, u0elo1]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    rcases p6884_3 (m.d 0 2) (by simp) with h6888 | h6888
                                                    · rcases p6884_3 (m.d 1 2) (by simp) with h6889 | h6889
                                                      · rcases p6884_3 (m.d 2 3) (by simp) with h6890 | h6890
                                                        · linarith only [h6683, h6890, hlam]
                                                        · linarith only [h6781, h6890, hlam]
                                                      · linarith only [h6775, h6889, hlam]
                                                    · linarith only [h6888, hlam, p6884_0]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    rcases p6884_3 (m.d 0 2) (by simp) with h6895 | h6895
                                                    · rcases p6884_3 (m.d 1 2) (by simp) with h6896 | h6896
                                                      · rcases p6884_3 (m.d 2 3) (by simp) with h6897 | h6897
                                                        · linarith only [h6683, h6897, hlam]
                                                        · linarith only [h6782, h6897, hlam]
                                                      · linarith only [h6776, h6896, hlam]
                                                    · linarith only [h6895, hlam, p6884_0]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [h0, h6681, h6682, h6775, h6781, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6787_1, p6884_1]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [hlam, p6884_0]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    rcases p6884_3 (m.d 0 2) (by simp) with h6904 | h6904
                                                    · linarith only [h0, h6904, hlam]
                                                    · linarith only [h6683, h6904, hlam]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [h0, h6681, h6682, h6775, hlam, p6787_1, p6884_2]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    rcases p6884_3 (m.d 0 2) (by simp) with h6908 | h6908
                                                    · linarith only [h0, h6908, hlam]
                                                    · linarith only [h6685, h6908, hlam]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [h6683, hlam, p6884_0]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [h6774, hlam, p6884_0]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [hlam, p6884_0]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [h6683, h6781, hc34, hlam, hphi, ht0b, ht45, ht5b, p6884_1, u0elo1]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [h6683, hc25, hlam, hphi, ht0b, ht5b, p6884_1, u0elo1]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [h6684, hlam, p6884_0]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [h6775, hlam, p6884_0]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [h6781, hlam, p6884_1]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [hlam, p6884_0]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [h6783, hlam, p6884_1]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [h6685, hlam, p6884_0]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [h6776, hlam, p6884_0]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [h6782, hlam, p6884_1]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [h6685, h6781, hc34, hlam, hphi, ht0b, ht45, ht5b, p6884_1, u0elo1]
                                                  · have p6884_0 := h6884c.1
                                                    have p6884_1 := h6884c.2.1
                                                    have p6884_2 := h6884c.2.2.1
                                                    have p6884_3 := h6884c.2.2.2
                                                    linarith only [hlam, p6884_0]
                                                · linarith only [h6688, h6883, hlam]
                                            · linarith only [h6686, h6880, hlam]
                                          · linarith only [h6684, h6879, hlam]
                                        · linarith only [h6681, h6878, hlam]
                                      · have p6787_0 := h6787c.1
                                        have p6787_1 := h6787c.2.1
                                        have p6787_2 := h6787c.2.2.1
                                        have p6787_3 := h6787c.2.2.2
                                        linarith only [hlam, p6787_0]
                                · linarith only [h4610, h6682, h6774, h6778, h6781, h6782, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6932 | h6932
                                · linarith only [h6683, h6686, h6781, h6932, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6934 | h6934
                                  · linarith only [h4610, h6682, h6688, h6774, h6777, h6779, h6781, h6934, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6936 | h6936
                                    · linarith only [h6681, h6688, h6777, h6936, hlam]
                                    · rcases h0bigk with h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c | h6938c
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [hlam, p6938_0]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h0, hlam, p6938_1]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h4610, hlam, p6938_0]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h4610, h6681, h6774, h6777, h6781, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6938_1]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h4610, h6687, h6774, h6781, h6936, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6938_1]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h6681, h6777, h6781, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6938_1, u0elo1]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [hlam, p6938_0]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h4610, h6681, h6777, h6781, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6938_1, u0elo1]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h6681, h6777, h6781, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6938_1, u0elo1]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h6687, h6781, h6936, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6938_1, u0elo1]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h6681, h6777, h6781, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6938_1, u0elo2]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h6683, hlam, p6938_1]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [hlam, p6938_0]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h6681, h6683, h6777, h6781, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6938_1, u0elo1]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h6683, h6687, h6781, h6936, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6938_1, u0elo1]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h6681, hlam, p6938_0]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h6684, hlam, p6938_0]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h6686, hlam, p6938_0]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [hlam, p6938_0]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h6688, hlam, p6938_0]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h6682, hlam, p6938_0]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h6685, hlam, p6938_1]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h6687, hlam, p6938_0]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [h6681, h6777, h6781, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6938_1, u0elo4]
                                      · have p6938_0 := h6938c.1
                                        have p6938_1 := h6938c.2.1
                                        have p6938_2 := h6938c.2.2.1
                                        have p6938_3 := h6938c.2.2.2
                                        linarith only [hlam, p6938_0]
                          · linarith only [h4610, h6687, h6778, hlam]
                        · linarith only [h4610, h6686, h6777, hlam]
                      · linarith only [h0, h6685, h6776, hlam]
                    · linarith only [h4610, h6684, h6774, h6775, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h6683, h6774, hlam]
              · linarith only [h4610, h6682, h6687, hlam]
            · linarith only [h4610, h6681, h6686, hlam]
          · linarith only [h0, h6682, h6685, hlam]
        · linarith only [h4610, h6681, h6683, h6684, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h6973 | h6973
        · rcases m.htr 0 2 5 (by decide) (by decide) with h6974 | h6974
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6975 | h6975
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6976 | h6976
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6977 | h6977
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6978 | h6978
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6979 | h6979
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6980 | h6980
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6981 | h6981
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6982 | h6982
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6983 | h6983
                            · linarith only [h0, h6681, h6683, h6978, h6983, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h6681, h6683, h6977, h6978, h6983, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h6683, h6976, h6978, h6982, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h6683, h6975, h6978, h6981, hlam]
                      · linarith only [h6683, h6974, h6980, hc12, hc23, hlam, hphi]
                    · linarith only [h6683, h6978, h6979, hc02, hc24, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6990 | h6990
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6991 | h6991
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6992 | h6992
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6993 | h6993
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6994 | h6994
                            · linarith only [h0, h6681, h6978, h6994, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h6681, h6977, h6978, h6992, h6994, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h4610, h6976, h6993, hlam]
                        · linarith only [h4610, h6975, h6992, hlam]
                      · linarith only [h0, h6974, h6991, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h6973, h6990, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7001 | h7001
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7002 | h7002
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7003 | h7003
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7004 | h7004
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7005 | h7005
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7006 | h7006
                            · linarith only [h6681, h6977, h7006, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7008 | h7008
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7009 | h7009
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7010 | h7010
                                  · linarith only [h6681, h6977, h7002, h7010, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7012 | h7012
                                    · linarith only [h6681, h6977, h7002, h7008, h7012, hlam]
                                    · rcases h0bigk with h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c | h7014c
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [hlam, p7014_0]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h0, hlam, p7014_1]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h4610, hlam, p7014_0]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h0, h6681, h6683, h7001, h7002, h7008, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7014_1]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h0, h6683, h7001, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7014_1]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h6683, h7001, hc01, hc12, hlam, hphi, p7014_1]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [hlam, p7014_0]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h6683, hlam, p7014_0]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h6681, h6683, h7001, h7002, h7008, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7014_1]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h6682, h6683, h7001, h7002, h7006, h7008, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7014_1]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h6682, h7002, h7006, h7008, hc34, hlam, hphi, ht0b, ht45, ht5b, p7014_1, u0elo2]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h0, h6682, h6683, h7001, h7002, h7006, h7008, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7014_1]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [hlam, p7014_0]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        rcases p7014_3 (m.d 0 1) (by simp) with h7028 | h7028
                                        · linarith only [h4610, h7028, hlam]
                                        · linarith only [h6681, h7028, hlam]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        rcases p7014_3 (m.d 0 1) (by simp) with h7031 | h7031
                                        · linarith only [h4610, h7031, hlam]
                                        · linarith only [h6682, h7031, hlam]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h6681, hlam, p7014_0]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h6973, hlam, p7014_0]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h6975, hlam, p7014_0]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [hlam, p7014_0]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h6977, hlam, p7014_0]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h6682, hlam, p7014_0]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h6974, hlam, p7014_1]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h6976, hlam, p7014_0]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [h0, h6681, h6682, h6683, h7001, h7002, h7008, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7014_1]
                                      · have p7014_0 := h7014c.1
                                        have p7014_1 := h7014c.2.1
                                        have p7014_2 := h7014c.2.2.1
                                        have p7014_3 := h7014c.2.2.2
                                        linarith only [hlam, p7014_0]
                                · linarith only [h6683, h6976, h7009, hlam]
                              · linarith only [h6683, h6975, h7008, hlam]
                          · linarith only [h4610, h6976, h7005, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h6683, h6975, h7001, h7004, hlam]
                      · linarith only [h0, h6974, h7003, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h6683, h7001, h7002, hc02, hc24, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7050 | h7050
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7051 | h7051
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7052 | h7052
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7053 | h7053
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7054 | h7054
                            · linarith only [h6681, h6977, h7054, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7056 | h7056
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7057 | h7057
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7058 | h7058
                                  · linarith only [h6681, h6977, h7050, h7058, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7060 | h7060
                                    · linarith only [h6681, h6977, h7050, h7056, h7060, hlam]
                                    · rcases h0bigk with h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c | h7062c
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [hlam, p7062_0]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [h0, hlam, p7062_1]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [h4610, hlam, p7062_0]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [h0, h6681, h7001, h7050, h7056, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7062_1]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [h0, h7001, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7062_1]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [h0, h7001, hc01, hc23, hlam, hphi, ht12, p7062_1]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [hlam, p7062_0]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [h6683, hlam, p7062_0]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        rcases p7062_3 (m.d 0 1) (by simp) with h7071 | h7071
                                        · linarith only [h0, h7071, hlam]
                                        · linarith only [h6681, h7071, hlam]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        rcases p7062_3 (m.d 0 1) (by simp) with h7074 | h7074
                                        · linarith only [h0, h7074, hlam]
                                        · linarith only [h6682, h7074, hlam]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [h6682, h7050, h7054, h7056, hc34, hlam, hphi, ht0b, ht45, ht5b, p7062_1, u0elo2]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [h0, h6682, h7050, h7054, h7056, hc34, hlam, hphi, ht0b, ht45, ht5b, p7062_1, u0elo2]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [hlam, p7062_0]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        rcases p7062_3 (m.d 0 1) (by simp) with h7080 | h7080
                                        · linarith only [h4610, h7080, hlam]
                                        · linarith only [h6681, h7080, hlam]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        rcases p7062_3 (m.d 0 1) (by simp) with h7083 | h7083
                                        · linarith only [h4610, h7083, hlam]
                                        · linarith only [h6682, h7083, hlam]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [h6681, hlam, p7062_0]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [h6973, hlam, p7062_0]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [h6975, hlam, p7062_0]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [hlam, p7062_0]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [h6977, hlam, p7062_0]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [h6682, hlam, p7062_0]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [h6974, hlam, p7062_1]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [h6976, hlam, p7062_0]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [h0, h6681, h6682, h7001, h7050, h7056, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7062_1]
                                      · have p7062_0 := h7062c.1
                                        have p7062_1 := h7062c.2.1
                                        have p7062_2 := h7062c.2.2.1
                                        have p7062_3 := h7062c.2.2.2
                                        linarith only [hlam, p7062_0]
                                · linarith only [h0, h7001, h7057, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h7001, h7056, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h4610, h6976, h7053, hlam]
                        · linarith only [h4610, h6975, h7052, hlam]
                      · linarith only [h0, h6681, h6974, h7050, h7051, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h0, h6973, h7050, hlam]
              · linarith only [h4610, h6682, h6976, hlam]
            · linarith only [h0, h6681, h6683, h6975, hlam]
          · linarith only [h0, h6682, h6974, hlam]
        · linarith only [h0, h6681, h6973, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h7106 | h7106
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7107 | h7107
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7108 | h7108
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7109 | h7109
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7110 | h7110
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7111 | h7111
                · linarith only [h6681, h6682, h7111, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7113 | h7113
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7114 | h7114
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7115 | h7115
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7116 | h7116
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7117 | h7117
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7118 | h7118
                            · linarith only [h6681, h7111, h7118, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7120 | h7120
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7121 | h7121
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7122 | h7122
                                  · linarith only [h6682, h7107, h7118, h7122, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7124 | h7124
                                    · linarith only [h6681, h6682, h7114, h7118, h7120, h7124, hlam]
                                    · rcases h0bigk with h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c | h7126c
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [hlam, p7126_0]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [h0, hlam, p7126_1]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [h4610, hlam, p7126_0]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [h6681, h6682, h7114, h7118, h7120, hc34, hc45, hlam, hphi, p7126_1]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [h6682, hlam, p7126_1]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [h6681, h7114, h7120, hc34, hlam, hphi, ht0b, ht45, ht5b, p7126_1, u0elo1]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [hlam, p7126_0]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [h4610, h6681, h7114, h7120, hc34, hlam, hphi, ht0b, ht45, ht5b, p7126_1, u0elo1]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        rcases p7126_3 (m.d 0 1) (by simp) with h7135 | h7135
                                        · linarith only [h0, h7135, hlam]
                                        · linarith only [h6681, h7135, hlam]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [h6681, h6682, h7114, h7120, hc34, hlam, hphi, ht0b, ht45, ht5b, p7126_1, u0elo1]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [h6681, h7114, h7120, hc34, hlam, hphi, ht0b, ht45, ht5b, p7126_1, u0elo2]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [h7106, hlam, p7126_1]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [hlam, p7126_0]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        rcases p7126_3 (m.d 0 1) (by simp) with h7142 | h7142
                                        · linarith only [h4610, h7142, hlam]
                                        · linarith only [h6681, h7142, hlam]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [h6681, h6682, h7106, h7114, h7120, hc34, hlam, hphi, ht0b, ht45, ht5b, p7126_1, u0elo1]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [h6681, hlam, p7126_0]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [h7107, hlam, p7126_0]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [h7109, hlam, p7126_0]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [hlam, p7126_0]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [h7111, hlam, p7126_0]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [h6681, h7114, h7120, hc34, hlam, hphi, ht0b, ht45, ht5b, p7126_1, u0elo4]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [h7108, hlam, p7126_1]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [h7110, hlam, p7126_0]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        rcases p7126_3 (m.d 0 1) (by simp) with h7154 | h7154
                                        · linarith only [h6682, h7154, hlam]
                                        · linarith only [h6681, h7154, hlam]
                                      · have p7126_0 := h7126c.1
                                        have p7126_1 := h7126c.2.1
                                        have p7126_2 := h7126c.2.2.1
                                        have p7126_3 := h7126c.2.2.2
                                        linarith only [hlam, p7126_0]
                                · linarith only [h7106, h7110, h7120, h7121, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h6681, h6682, h7116, h7118, h7120, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h4610, h7106, h7110, h7117, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h4610, h7109, h7116, hlam]
                      · linarith only [h0, h7108, h7115, hlam]
                    · linarith only [h0, h7107, h7114, hlam]
                  · linarith only [h0, h7106, h7113, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7165 | h7165
                · linarith only [h4610, h6681, h7110, h7165, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7167 | h7167
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7168 | h7168
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7169 | h7169
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7170 | h7170
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7171 | h7171
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7172 | h7172
                            · linarith only [h6681, h7165, h7172, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7174 | h7174
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7175 | h7175
                                · linarith only [h4610, h7106, h7110, h7175, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7177 | h7177
                                  · linarith only [h4610, h6681, h7110, h7168, h7171, h7172, h7177, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7179 | h7179
                                    · linarith only [h4610, h6681, h7110, h7168, h7171, h7172, h7174, h7179, hlam]
                                    · rcases h0bigk with h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h0, hlam, p7181_1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h4610, hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h4610, h6681, h7110, h7167, h7168, h7171, h7174, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7181_1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h6682, hlam, p7181_1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h6681, h7168, h7174, hc34, hlam, hphi, ht0b, ht45, ht5b, p7181_1, u0elo1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h4610, h6681, h7168, h7174, hc34, hlam, hphi, ht0b, ht45, ht5b, p7181_1, u0elo1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        rcases p7181_3 (m.d 0 1) (by simp) with h7190 | h7190
                                        · linarith only [h0, h7190, hlam]
                                        · linarith only [h6681, h7190, hlam]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h4610, h6681, h7110, h7168, h7174, hc34, hlam, hphi, ht0b, ht45, ht5b, p7181_1, u0elo1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h6681, h7168, h7174, hc34, hlam, hphi, ht0b, ht45, ht5b, p7181_1, u0elo2]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h7106, hlam, p7181_1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h6681, h7110, h7167, h7168, h7171, h7174, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7181_1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h7110, hlam, p7181_1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h6681, hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h7107, hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h7109, hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h7165, hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h6681, h7108, h7168, h7174, hc34, hlam, hphi, ht0b, ht45, ht5b, p7181_1, u0elo1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h7108, hlam, p7181_1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h4610, h6681, h7110, h7167, h7168, h7171, h7174, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7181_1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        rcases p7181_3 (m.d 0 1) (by simp) with h7207 | h7207
                                        · linarith only [h6682, h7207, hlam]
                                        · linarith only [h6681, h7207, hlam]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [hlam, p7181_0]
                              · linarith only [h7109, h7110, h7167, h7171, h7174, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7212 | h7212
                            · linarith only [h4610, h6681, h7171, h7212, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7214 | h7214
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7215 | h7215
                                · linarith only [h4610, h6681, h7168, h7171, h7214, h7215, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7217 | h7217
                                  · linarith only [h4610, h6681, h6682, h7168, h7171, h7212, h7217, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7219 | h7219
                                    · linarith only [h4610, h6681, h7168, h7171, h7212, h7214, h7219, hlam]
                                    · linarith only [h4610, h6681, h7168, h7171, h7214, h7219, hc34, hc45, hlam, hphi]
                              · linarith only [h4610, h7109, h7171, h7214, hc23, hc35, hlam, hphi]
                        · linarith only [h4610, h6681, h7109, h7168, h7170, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h0, h6681, h7108, h7168, h7169, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · linarith only [h0, h7107, h7168, hlam]
                  · linarith only [h0, h7106, h7167, hlam]
            · linarith only [h4610, h6681, h7109, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7228 | h7228
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7229 | h7229
              · linarith only [h7106, h7108, h7229, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7231 | h7231
                · linarith only [h0, h6681, h7108, h7231, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7233 | h7233
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7234 | h7234
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7235 | h7235
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7236 | h7236
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7237 | h7237
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7238 | h7238
                            · linarith only [h6681, h7231, h7238, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7240 | h7240
                              · linarith only [h7106, h7108, h7235, h7240, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h7106, h7108, h7228, h7235, h7240, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7243 | h7243
                            · linarith only [h4610, h6681, h7106, h7108, h7235, h7243, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7245 | h7245
                              · linarith only [h7106, h7108, h7235, h7245, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h7106, h7108, h7228, h7235, h7245, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h4610, h6681, h7228, h7236, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7249 | h7249
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7250 | h7250
                          · linarith only [h4610, h6681, h7229, h7233, h7234, h7235, h7250, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7252 | h7252
                            · linarith only [h0, h6681, h7235, h7252, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7254 | h7254
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7255 | h7255
                                · linarith only [h7106, h7250, h7255, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7257 | h7257
                                  · linarith only [h0, h4610, h6681, h7106, h7234, h7235, h7252, h7257, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                  · linarith only [h4610, h6681, h7233, h7234, h7235, h7254, h7257, hc34, hc45, hlam, hphi]
                              · linarith only [h7228, h7229, h7254, hc23, hc35, hlam, hphi]
                        · linarith only [h4610, h7228, h7229, h7249, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h7107, h7234, hlam]
                  · linarith only [h0, h7106, h7233, hlam]
            · linarith only [h4610, h6681, h7228, hlam]
        · linarith only [h4610, h6681, h7106, h7107, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7266 | h7266
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7267 | h7267
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7268 | h7268
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7269 | h7269
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7270 | h7270
                · linarith only [h6681, h6682, h7270, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7272 | h7272
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7273 | h7273
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7274 | h7274
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7275 | h7275
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7276 | h7276
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7277 | h7277
                            · linarith only [h6681, h7270, h7277, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7279 | h7279
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7280 | h7280
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7281 | h7281
                                  · linarith only [h6681, h6682, h7106, h7267, h7272, h7273, h7277, h7281, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7283 | h7283
                                    · linarith only [h6681, h6682, h7273, h7277, h7279, h7283, hlam]
                                    · rcases h0bigk with h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c | h7285c
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [hlam, p7285_0]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h0, hlam, p7285_1]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h4610, hlam, p7285_0]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h6682, h7106, h7267, h7272, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p7285_1]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h6682, hlam, p7285_1]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h7106, h7272, hc01, hc12, hlam, hphi, p7285_1]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [hlam, p7285_0]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h7106, hlam, p7285_0]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h6681, h7106, h7272, h7273, h7279, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7285_1]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h7106, h7272, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7285_1]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h6681, h7273, h7279, hc34, hlam, hphi, ht0b, ht45, ht5b, p7285_1, u0elo2]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h7106, h7267, h7272, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p7285_1]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [hlam, p7285_0]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        rcases p7285_3 (m.d 0 1) (by simp) with h7299 | h7299
                                        · linarith only [h4610, h7299, hlam]
                                        · linarith only [h6681, h7299, hlam]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h6681, h6682, h7106, h7272, h7273, h7279, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7285_1]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h6681, hlam, p7285_0]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h7266, hlam, p7285_0]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h7268, hlam, p7285_0]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [hlam, p7285_0]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h7270, hlam, p7285_0]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h6681, h7267, h7273, h7279, hc34, hlam, hphi, ht0b, ht45, ht5b, p7285_1, u0elo1]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h7267, hlam, p7285_1]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h7269, hlam, p7285_0]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [h6681, h7106, h7267, h7272, h7273, h7279, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7285_1]
                                      · have p7285_0 := h7285c.1
                                        have p7285_1 := h7285c.2.1
                                        have p7285_2 := h7285c.2.2.1
                                        have p7285_3 := h7285c.2.2.2
                                        linarith only [hlam, p7285_0]
                                · linarith only [h7106, h7269, h7280, hlam]
                              · linarith only [h7106, h7268, h7279, hlam]
                          · linarith only [h7106, h7267, h7269, h7272, h7276, hlam]
                        · linarith only [h7106, h7268, h7272, h7275, hlam]
                      · linarith only [h7106, h7267, h7274, hc12, hc23, hlam, hphi]
                    · linarith only [h6682, h7106, h7267, h7272, h7273, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7319 | h7319
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7320 | h7320
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7321 | h7321
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7322 | h7322
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7323 | h7323
                            · linarith only [h6681, h6682, h7272, h7320, h7323, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7325 | h7325
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7326 | h7326
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7327 | h7327
                                  · linarith only [h6681, h6682, h7319, h7323, h7327, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7329 | h7329
                                    · linarith only [h6681, h6682, h7319, h7323, h7325, h7329, hlam]
                                    · rcases h0bigk with h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c | h7331c
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [hlam, p7331_0]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [h0, hlam, p7331_1]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [h4610, hlam, p7331_0]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [h6682, h7272, h7320, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7331_1]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [h6682, hlam, p7331_1]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [h0, h7272, hc01, hc23, hlam, hphi, ht12, p7331_1]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [hlam, p7331_0]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [h7106, hlam, p7331_0]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        rcases p7331_3 (m.d 0 1) (by simp) with h7340 | h7340
                                        · linarith only [h0, h7340, hlam]
                                        · linarith only [h6681, h7340, hlam]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [h0, h6681, h6682, h7272, h7319, h7325, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7331_1]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [h6681, h7319, h7325, hc34, hlam, hphi, ht0b, ht45, ht5b, p7331_1, u0elo2]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [h7267, hc25, hlam, hphi, ht0b, ht5b, p7331_1, u0elo2]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [hlam, p7331_0]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        rcases p7331_3 (m.d 0 1) (by simp) with h7347 | h7347
                                        · linarith only [h4610, h7347, hlam]
                                        · linarith only [h6681, h7347, hlam]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [h6681, h6682, h7319, h7325, hc34, hlam, hphi, ht0b, ht45, ht5b, p7331_1, u0elo2]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [h6681, hlam, p7331_0]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [h7266, hlam, p7331_0]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [h7268, hlam, p7331_0]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [hlam, p7331_0]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [h7270, hlam, p7331_0]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [h6681, h7267, h7319, h7325, hc34, hlam, hphi, ht0b, ht45, ht5b, p7331_1, u0elo1]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [h7267, hlam, p7331_1]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [h7269, hlam, p7331_0]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        rcases p7331_3 (m.d 0 1) (by simp) with h7359 | h7359
                                        · linarith only [h6682, h7359, hlam]
                                        · linarith only [h6681, h7359, hlam]
                                      · have p7331_0 := h7331c.1
                                        have p7331_1 := h7331c.2.1
                                        have p7331_2 := h7331c.2.2.1
                                        have p7331_3 := h7331c.2.2.2
                                        linarith only [hlam, p7331_0]
                                · linarith only [h0, h6681, h7272, h7319, h7325, h7326, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h6681, h6682, h7272, h7319, h7320, h7325, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h4610, h6681, h7267, h7269, h7319, h7322, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h4610, h7268, h7321, hlam]
                      · linarith only [h0, h7267, h7320, hlam]
                    · linarith only [h0, h7266, h7319, hlam]
              · linarith only [h7106, h7267, h7269, hlam]
            · linarith only [h0, h6681, h7106, h7268, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7371 | h7371
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7372 | h7372
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7373 | h7373
                · linarith only [h0, h6681, h7267, h7373, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7375 | h7375
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7376 | h7376
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7377 | h7377
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7378 | h7378
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7379 | h7379
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7380 | h7380
                            · linarith only [h6681, h7373, h7380, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7382 | h7382
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7383 | h7383
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7384 | h7384
                                  · linarith only [h0, h6681, h7267, h7375, h7376, h7380, h7383, h7384, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7386 | h7386
                                    · linarith only [h0, h6681, h7267, h7376, h7377, h7380, h7382, h7386, hlam]
                                    · rcases h0bigk with h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [hlam, p7388_0]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h0, hlam, p7388_1]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h4610, hlam, p7388_0]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h0, h6681, h7267, h7375, h7376, h7382, h7383, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7388_1]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h6682, hlam, p7388_1]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h7267, h7375, h7383, hc01, hc12, hlam, hphi, p7388_1]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [hlam, p7388_0]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h7106, hlam, p7388_0]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h6681, h7267, h7375, h7376, h7382, h7383, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7388_1]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h7267, hlam, p7388_0]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h6681, h7106, h7375, h7376, h7382, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7388_1]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h0, h6681, h7106, h7375, h7376, h7382, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7388_1]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [hlam, p7388_0]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        rcases p7388_3 (m.d 0 1) (by simp) with h7402 | h7402
                                        · linarith only [h4610, h7402, hlam]
                                        · linarith only [h6681, h7402, hlam]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h6681, h6682, h7106, h7375, h7376, h7382, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7388_1]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h6681, hlam, p7388_0]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h7266, hlam, p7388_0]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h7371, hlam, p7388_0]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [hlam, p7388_0]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h7373, hlam, p7388_0]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h6681, h7376, h7382, hc34, hlam, hphi, ht0b, ht45, ht5b, p7388_1, u0elo4]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h0, h6681, h7267, h7375, h7376, h7382, h7383, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7388_1]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [h7372, hlam, p7388_0]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        rcases p7388_3 (m.d 0 1) (by simp) with h7414 | h7414
                                        · linarith only [h6682, h7414, hlam]
                                        · linarith only [h6681, h7414, hlam]
                                      · have p7388_0 := h7388c.1
                                        have p7388_1 := h7388c.2.1
                                        have p7388_2 := h7388c.2.2.1
                                        have p7388_3 := h7388c.2.2.2
                                        linarith only [hlam, p7388_0]
                                · linarith only [h7106, h7372, h7383, hlam]
                              · linarith only [h7106, h7371, h7382, hlam]
                          · linarith only [h4610, h6681, h7372, h7376, h7379, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h7106, h7371, h7375, h7378, hlam]
                      · linarith only [h7106, h7375, h7377, hc02, hc25, hlam, hphi]
                    · linarith only [h0, h6681, h7106, h7375, h7376, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7424 | h7424
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7425 | h7425
                      · linarith only [h0, h6681, h7267, h7375, h7424, h7425, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7427 | h7427
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7428 | h7428
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7429 | h7429
                            · linarith only [h0, h6681, h7373, h7375, h7429, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7431 | h7431
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7432 | h7432
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7433 | h7433
                                  · linarith only [h0, h6681, h7424, h7425, h7429, h7432, h7433, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · linarith only [h0, h6681, h7425, h7433, hc14, hc45, hlam, hphi]
                                · linarith only [h0, h6681, h7106, h7372, h7424, h7431, h7432, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                              · linarith only [h0, h7375, h7431, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h4610, h6681, h7372, h7424, h7428, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h4610, h7371, h7427, hlam]
                    · linarith only [h0, h7266, h7424, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7441 | h7441
                · linarith only [h6681, h6682, h7441, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7443 | h7443
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7444 | h7444
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7445 | h7445
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7446 | h7446
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7447 | h7447
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7448 | h7448
                            · linarith only [h6681, h7441, h7448, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7450 | h7450
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7451 | h7451
                                · linarith only [h0, h7106, h7372, h7443, h7451, hc01, hc12, hlam, hphi]
                                · linarith only [h0, h6681, h7106, h7443, h7444, h7447, h7450, h7451, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h7106, h7371, h7450, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7455 | h7455
                            · linarith only [h4610, h6681, h7441, h7447, h7455, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7457 | h7457
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7458 | h7458
                                · linarith only [h7443, h7447, h7458, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7460 | h7460
                                  · linarith only [h0, h6681, h7106, h7443, h7444, h7447, h7455, h7460, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7462 | h7462
                                    · linarith only [h0, h6681, h7106, h7443, h7444, h7447, h7455, h7457, h7462, hlam]
                                    · linarith only [h0, h6681, h7106, h7443, h7444, h7447, h7457, h7462, hc34, hc45, hlam, hphi]
                              · linarith only [h0, h6681, h7106, h7371, h7444, h7457, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h0, h6681, h7106, h7371, h7443, h7444, h7446, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · linarith only [h0, h6681, h7106, h7443, h7444, h7445, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h6681, h7106, h7443, h7444, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7469 | h7469
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7470 | h7470
                      · linarith only [h0, h6681, h7267, h7443, h7469, h7470, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7472 | h7472
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7473 | h7473
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7474 | h7474
                            · linarith only [h0, h6681, h7443, h7474, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7476 | h7476
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7477 | h7477
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7478 | h7478
                                  · linarith only [h0, h6681, h7106, h7372, h7443, h7469, h7470, h7473, h7474, h7478, hc12, hc23, hlam, hphi]
                                  · linarith only [h0, h6681, h7469, h7470, h7476, h7478, hc34, hc45, hlam, hphi]
                                · linarith only [h7443, h7473, h7477, hlam]
                              · linarith only [h0, h6681, h7106, h7372, h7443, h7469, h7473, h7476, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7483 | h7483
                            · linarith only [h0, h6681, h7443, h7473, h7483, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7485 | h7485
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7486 | h7486
                                · linarith only [h0, h6681, h7443, h7469, h7473, h7485, h7486, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h6681, h7443, h7469, h7485, h7486, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h6681, h7443, h7469, h7485, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h6681, h7371, h7443, h7469, h7472, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h0, h7266, h7469, hlam]
            · linarith only [h4610, h6681, h7371, hlam]
        · linarith only [h0, h6681, h7266, hlam]
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s6 m hb0 hb2 hb3 hb5 h0 h4610 h6681

end R2N4
