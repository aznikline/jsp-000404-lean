import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 19434000 in
set_option maxHeartbeats 19434000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h22350 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h30132 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h30701 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h18443 := hg18443
  have h20697 := hg20697
  rcases m.htr 0 3 4 (by decide) (by decide) with h30702 | h30702
  · rcases m.htr 0 3 5 (by decide) (by decide) with h30703 | h30703
    · rcases m.htr 0 4 5 (by decide) (by decide) with h30704 | h30704
      · rcases m.htr 1 2 3 (by decide) (by decide) with h30705 | h30705
        · rcases m.htr 1 2 4 (by decide) (by decide) with h30706 | h30706
          · rcases m.htr 1 2 5 (by decide) (by decide) with h30707 | h30707
            · rcases m.htr 1 3 4 (by decide) (by decide) with h30708 | h30708
              · rcases m.htr 1 3 5 (by decide) (by decide) with h30709 | h30709
                · rcases m.htr 1 4 5 (by decide) (by decide) with h30710 | h30710
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h30711 | h30711
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h30712 | h30712
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h30713 | h30713
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h30714 | h30714
                          · rcases h0bigk with h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c | h30715c
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [hlam, p30715_0]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h0, hlam, p30715_1]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h15532, hlam, p30715_0]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h18443, hlam, p30715_1]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h20697, hlam, p30715_1]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h30132, h30706, h30708, hc01, hc13, hlam, hphi, p30715_1]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [hlam, p30715_0]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h22350, hlam, p30715_0]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h30132, hlam, p30715_1]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h20697, h30132, h30706, h30708, hc01, hc13, hlam, hphi, p30715_1]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h22350, h30705, hc01, hc12, hlam, hphi, p30715_1]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h22350, h30701, h30705, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p30715_1]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [hlam, p30715_0]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h18443, h22350, h30705, hc01, hc12, hlam, hphi, p30715_1]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h20697, h22350, h30705, hc01, hc12, hlam, hphi, p30715_1]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h22350, h30702, h30705, hc01, hc12, hlam, hphi, p30715_1]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h22350, h30701, h30702, h30705, h30712, h30714, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p30715_1]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h30702, hlam, p30715_0]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [hlam, p30715_0]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h20697, h22350, h30702, h30705, hc01, hc12, hlam, hphi, p30715_1]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h22350, h30701, h30705, hc01, hc12, hlam, hphi, p30715_1]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h30701, hlam, p30715_1]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h30703, hlam, p30715_0]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [h30704, hlam, p30715_1]
                            · have p30715_0 := h30715c.1
                              have p30715_1 := h30715c.2.1
                              have p30715_2 := h30715c.2.2.1
                              have p30715_3 := h30715c.2.2.2
                              linarith only [hlam, p30715_0]
                          · linarith only [h30132, h30701, h30705, h30711, h30713, h30714, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h22350, h30132, h30702, h30704, h30705, h30713, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h22350, h30703, h30712, hlam]
                    · linarith only [h22350, h30702, h30711, hlam]
                  · linarith only [h18443, h30132, h30701, h30704, h30710, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h15532, h30703, h30709, hlam]
              · linarith only [h15532, h30702, h30708, hlam]
            · linarith only [h22350, h30701, h30702, h30705, h30707, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h22350, h30701, h30705, h30706, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h30750 | h30750
          · linarith only [h30132, h30701, h30705, h30750, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h30752 | h30752
            · rcases m.htr 1 3 4 (by decide) (by decide) with h30753 | h30753
              · rcases m.htr 1 3 5 (by decide) (by decide) with h30754 | h30754
                · rcases m.htr 1 4 5 (by decide) (by decide) with h30755 | h30755
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h30756 | h30756
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h30757 | h30757
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h30758 | h30758
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h30759 | h30759
                          · rcases h0bigk with h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c | h30760c
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [hlam, p30760_0]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [h0, hlam, p30760_1]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [h15532, hlam, p30760_0]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [h18443, hlam, p30760_1]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [h20697, hlam, p30760_1]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [h0, h30750, h30756, hc01, hc23, hlam, hphi, ht12, p30760_1]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [hlam, p30760_0]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [h22350, hlam, p30760_0]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [h30132, hlam, p30760_1]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [h0, h20697, h30750, h30756, hc01, hc23, hlam, hphi, ht12, p30760_1]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              rcases p30760_3 (m.d 0 1) (by simp) with h30771 | h30771
                              · linarith only [h15532, h30771, hlam]
                              · rcases p30760_3 (m.d 0 2) (by simp) with h30773 | h30773
                                · linarith only [h22350, h30773, hlam]
                                · linarith only [h0, h30773, hlam]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              rcases p30760_3 (m.d 0 1) (by simp) with h30776 | h30776
                              · linarith only [h15532, h30776, hlam]
                              · rcases p30760_3 (m.d 0 2) (by simp) with h30778 | h30778
                                · linarith only [h22350, h30778, hlam]
                                · rcases p30760_3 (m.d 0 3) (by simp) with h30780 | h30780
                                  · rcases p30760_3 (m.d 0 4) (by simp) with h30781 | h30781
                                    · linarith only [h30702, h30781, hlam]
                                    · linarith only [h30132, h30781, hlam]
                                  · linarith only [h22350, h30780, hlam]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [hlam, p30760_0]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              rcases p30760_3 (m.d 0 1) (by simp) with h30786 | h30786
                              · linarith only [h15532, h30786, hlam]
                              · rcases p30760_3 (m.d 0 2) (by simp) with h30788 | h30788
                                · linarith only [h22350, h30788, hlam]
                                · rcases p30760_3 (m.d 0 3) (by simp) with h30790 | h30790
                                  · rcases p30760_3 (m.d 0 4) (by simp) with h30791 | h30791
                                    · linarith only [h30702, h30791, hlam]
                                    · rcases p30760_3 (m.d 0 5) (by simp) with h30793 | h30793
                                      · linarith only [h30703, h30793, hlam]
                                      · rcases h2bigk with h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c | h30795c
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [hlam, p30795_0]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [h0, hlam, p30795_1]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [h22350, hlam, p30795_0]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [h30132, hlam, p30795_0]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [h15532, h30132, h30705, h30757, h30759, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30760_1, p30795_1]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [h30750, h30756, hc02, hc23, hlam, hphi, p30795_1]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [hlam, p30795_0]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [h30705, hlam, p30795_0]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [h30750, hlam, p30795_0]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          rcases p30795_3 (m.d 0 2) (by simp) with h30805 | h30805
                                          · linarith only [h0, h30805, hlam]
                                          · linarith only [h30701, h30805, hlam]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          rcases p30795_3 (m.d 0 2) (by simp) with h30808 | h30808
                                          · linarith only [h30808, hlam, p30795_0]
                                          · rcases p30795_3 (m.d 1 2) (by simp) with h30810 | h30810
                                            · linarith only [h30705, h30810, hlam]
                                            · linarith only [h0, h30810, hlam]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p30795_1]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [hlam, p30795_0]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [h30132, h30701, h30757, h30759, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30795_1]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [h15532, h30132, h30701, h30705, hlam, p30760_1, p30795_2]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          rcases p30795_3 (m.d 0 2) (by simp) with h30817 | h30817
                                          · linarith only [h30817, hlam, p30795_0]
                                          · rcases p30795_3 (m.d 1 2) (by simp) with h30819 | h30819
                                            · linarith only [h30750, h30819, hlam]
                                            · linarith only [h0, h30819, hlam]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [h20697, h30752, h30756, hc01, hc23, hlam, hphi, ht12, p30795_1]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [h30756, hlam, p30795_1]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [hlam, p30795_0]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          rcases p30795_3 (m.d 0 2) (by simp) with h30825 | h30825
                                          · linarith only [h30132, h30825, hlam]
                                          · linarith only [h30701, h30825, hlam]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [h30701, hlam, p30795_0]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [h30752, hlam, p30795_0]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [h30757, hlam, p30795_1]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [h30758, hlam, p30795_0]
                                        · have p30795_0 := h30795c.1
                                          have p30795_1 := h30795c.2.1
                                          have p30795_2 := h30795c.2.2.1
                                          have p30795_3 := h30795c.2.2.2
                                          linarith only [hlam, p30795_0]
                                  · linarith only [h30702, h30790, hlam]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              rcases p30760_3 (m.d 0 1) (by simp) with h30834 | h30834
                              · linarith only [h15532, h30834, hlam]
                              · rcases p30760_3 (m.d 0 2) (by simp) with h30836 | h30836
                                · linarith only [h22350, h30836, hlam]
                                · linarith only [h30701, h30836, hlam]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              rcases p30760_3 (m.d 0 1) (by simp) with h30839 | h30839
                              · linarith only [h18443, h30839, hlam]
                              · rcases p30760_3 (m.d 0 2) (by simp) with h30841 | h30841
                                · linarith only [h30132, h30841, hlam]
                                · linarith only [h0, h30841, hlam]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              rcases p30760_3 (m.d 0 1) (by simp) with h30844 | h30844
                              · linarith only [h18443, h30844, hlam]
                              · rcases p30760_3 (m.d 0 2) (by simp) with h30846 | h30846
                                · linarith only [h30132, h30846, hlam]
                                · rcases p30760_3 (m.d 0 3) (by simp) with h30848 | h30848
                                  · rcases p30760_3 (m.d 0 4) (by simp) with h30849 | h30849
                                    · rcases p30760_3 (m.d 0 5) (by simp) with h30850 | h30850
                                      · linarith only [h30704, h30850, hlam]
                                      · rcases h2bigk with h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c | h30852c
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [hlam, p30852_0]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [h0, hlam, p30852_1]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [h22350, hlam, p30852_0]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [h30132, hlam, p30852_0]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [h15532, h30702, h30705, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p30760_1, p30852_1]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [h30705, hc02, hc23, hlam, hphi, p30852_1]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [hlam, p30852_0]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [h30705, hlam, p30852_0]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [h30750, hlam, p30852_0]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          rcases p30852_3 (m.d 0 2) (by simp) with h30862 | h30862
                                          · linarith only [h0, h30862, hlam]
                                          · linarith only [h30701, h30862, hlam]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          rcases p30852_3 (m.d 0 2) (by simp) with h30865 | h30865
                                          · linarith only [h30865, hlam, p30852_0]
                                          · rcases p30852_3 (m.d 1 2) (by simp) with h30867 | h30867
                                            · linarith only [h30705, h30867, hlam]
                                            · linarith only [h0, h30867, hlam]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p30852_1]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [hlam, p30852_0]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [h18443, h30750, hc01, hc23, hlam, hphi, ht12, p30852_1]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [h15532, h30701, h30702, h30705, hlam, p30760_1, p30852_2]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          rcases p30852_3 (m.d 0 2) (by simp) with h30874 | h30874
                                          · linarith only [h30874, hlam, p30852_0]
                                          · rcases p30852_3 (m.d 1 2) (by simp) with h30876 | h30876
                                            · linarith only [h30750, h30876, hlam]
                                            · linarith only [h0, h30876, hlam]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [h20697, h30752, hc01, hc24, hlam, hphi, ht12, p30852_1]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [h30756, hlam, p30852_1]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [hlam, p30852_0]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [h30132, h30701, hlam, p30760_1, p30852_2]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [h30701, hlam, p30852_0]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [h30752, hlam, p30852_0]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [h30757, hlam, p30852_1]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [h30758, hlam, p30852_0]
                                        · have p30852_0 := h30852c.1
                                          have p30852_1 := h30852c.2.1
                                          have p30852_2 := h30852c.2.2.1
                                          have p30852_3 := h30852c.2.2.2
                                          linarith only [hlam, p30852_0]
                                    · linarith only [h30132, h30849, hlam]
                                  · linarith only [h22350, h30848, hlam]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [h30702, hlam, p30760_0]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [hlam, p30760_0]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              rcases p30760_3 (m.d 0 1) (by simp) with h30892 | h30892
                              · linarith only [h18443, h30892, hlam]
                              · rcases p30760_3 (m.d 0 2) (by simp) with h30894 | h30894
                                · linarith only [h30132, h30894, hlam]
                                · linarith only [h30701, h30894, hlam]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [h22350, h30701, hc01, hc23, hlam, hphi, ht12, p30760_1]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [h30701, hlam, p30760_1]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [h30703, hlam, p30760_0]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [h30704, hlam, p30760_1]
                            · have p30760_0 := h30760c.1
                              have p30760_1 := h30760c.2.1
                              have p30760_2 := h30760c.2.2.1
                              have p30760_3 := h30760c.2.2.2
                              linarith only [hlam, p30760_0]
                          · rcases h0bigk with h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c | h30902c
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [hlam, p30902_0]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [h0, hlam, p30902_1]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [h15532, hlam, p30902_0]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [h18443, hlam, p30902_1]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [h20697, hlam, p30902_1]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [h0, h30750, h30756, hc01, hc23, hlam, hphi, ht12, p30902_1]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [hlam, p30902_0]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [h22350, hlam, p30902_0]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [h30132, hlam, p30902_1]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [h0, h20697, h30750, h30756, hc01, hc23, hlam, hphi, ht12, p30902_1]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              rcases p30902_3 (m.d 0 1) (by simp) with h30913 | h30913
                              · linarith only [h15532, h30913, hlam]
                              · rcases p30902_3 (m.d 0 2) (by simp) with h30915 | h30915
                                · linarith only [h22350, h30915, hlam]
                                · linarith only [h0, h30915, hlam]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [h15532, h30701, h30705, h30758, h30759, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30902_1]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [hlam, p30902_0]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [h15532, h30132, h30701, h30705, h30758, h30759, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30902_1]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              rcases p30902_3 (m.d 0 1) (by simp) with h30921 | h30921
                              · linarith only [h15532, h30921, hlam]
                              · rcases p30902_3 (m.d 0 2) (by simp) with h30923 | h30923
                                · linarith only [h22350, h30923, hlam]
                                · linarith only [h30701, h30923, hlam]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              rcases p30902_3 (m.d 0 1) (by simp) with h30926 | h30926
                              · linarith only [h18443, h30926, hlam]
                              · rcases p30902_3 (m.d 0 2) (by simp) with h30928 | h30928
                                · linarith only [h30132, h30928, hlam]
                                · linarith only [h0, h30928, hlam]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [h30701, h30758, h30759, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p30902_1]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [h30702, hlam, p30902_0]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [hlam, p30902_0]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              rcases p30902_3 (m.d 0 1) (by simp) with h30934 | h30934
                              · linarith only [h18443, h30934, hlam]
                              · rcases p30902_3 (m.d 0 2) (by simp) with h30936 | h30936
                                · linarith only [h30132, h30936, hlam]
                                · linarith only [h30701, h30936, hlam]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [h20697, h30750, h30752, h30756, hc01, hc23, hlam, hphi, ht12, p30902_1]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [h30701, hlam, p30902_1]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [h30703, hlam, p30902_0]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [h30704, hlam, p30902_1]
                            · have p30902_0 := h30902c.1
                              have p30902_1 := h30902c.2.1
                              have p30902_2 := h30902c.2.2.1
                              have p30902_3 := h30902c.2.2.2
                              linarith only [hlam, p30902_0]
                        · linarith only [h0, h30750, h30758, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h30750, h30756, h30757, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h20697, h30705, h30752, h30756, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h18443, h30132, h30701, h30704, h30755, hlam]
                · linarith only [h0, h15532, h30701, h30703, h30750, h30754, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h15532, h30702, h30753, hlam]
            · linarith only [h0, h30701, h30752, hlam]
      · linarith only [h30132, h30701, h30704, hlam]
    · linarith only [h22350, h30701, h30703, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h30953 | h30953
    · rcases m.htr 0 4 5 (by decide) (by decide) with h30954 | h30954
      · rcases m.htr 1 2 3 (by decide) (by decide) with h30955 | h30955
        · rcases m.htr 1 2 4 (by decide) (by decide) with h30956 | h30956
          · rcases m.htr 1 2 5 (by decide) (by decide) with h30957 | h30957
            · rcases m.htr 1 3 4 (by decide) (by decide) with h30958 | h30958
              · rcases m.htr 1 3 5 (by decide) (by decide) with h30959 | h30959
                · rcases m.htr 1 4 5 (by decide) (by decide) with h30960 | h30960
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h30961 | h30961
                    · linarith only [h22350, h30701, h30702, h30955, h30961, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h22350, h30701, h30955, h30958, h30961, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h18443, h30954, h30960, hlam]
                · linarith only [h15532, h30953, h30959, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h30966 | h30966
                · rcases m.htr 1 4 5 (by decide) (by decide) with h30967 | h30967
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h30968 | h30968
                    · linarith only [h30955, h30958, h30968, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h30970 | h30970
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h30971 | h30971
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h30972 | h30972
                          · rcases h0bigk with h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c | h30973c
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [hlam, p30973_0]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h0, hlam, p30973_1]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h15532, hlam, p30973_0]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h18443, hlam, p30973_1]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h20697, hlam, p30973_1]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h22350, h30955, h30958, hc01, hc34, hlam, hphi, ht12, ht23, p30973_1]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [hlam, p30973_0]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h22350, hlam, p30973_0]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h30132, hlam, p30973_1]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h22350, h30955, h30958, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p30973_1]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h22350, h30955, h30958, hc01, hc34, hlam, hphi, ht12, ht23, p30973_1]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h22350, h30955, h30958, hc02, hc34, hlam, hphi, ht23, p30973_1]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [hlam, p30973_0]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h30702, hlam, p30973_1]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h20697, h22350, h30955, h30958, hc01, hc34, hlam, hphi, ht12, ht23, p30973_1]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h30132, h30956, hc01, hc12, hlam, hphi, p30973_1]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h30132, h30701, h30956, h30970, h30972, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p30973_1]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h22350, h30132, h30701, h30956, h30970, h30972, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p30973_1]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [hlam, p30973_0]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h20697, h30132, h30956, hc01, hc12, hlam, hphi, p30973_1]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h15532, h22350, h30701, h30958, hc01, hc34, hlam, hphi, ht12, ht23, p30973_1]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h30701, hlam, p30973_1]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h30953, hlam, p30973_0]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [h30954, hlam, p30973_1]
                            · have p30973_0 := h30973c.1
                              have p30973_1 := h30973c.2.1
                              have p30973_2 := h30973c.2.2.1
                              have p30973_3 := h30973c.2.2.2
                              linarith only [hlam, p30973_0]
                          · linarith only [h22350, h30955, h30958, h30972, hc02, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h18443, h22350, h30132, h30701, h30954, h30955, h30958, h30971, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h15532, h22350, h30953, h30958, h30970, hc02, hc34, hlam, hphi, ht23]
                  · linarith only [h18443, h22350, h30701, h30954, h30955, h30958, h30967, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h15532, h30132, h30702, h30953, h30966, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h20697, h30132, h30701, h30956, h30957, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h20697, h22350, h30701, h30955, h30956, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h31006 | h31006
          · linarith only [h20697, h30132, h30701, h30955, h31006, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h31008 | h31008
            · rcases m.htr 1 3 4 (by decide) (by decide) with h31009 | h31009
              · rcases m.htr 1 3 5 (by decide) (by decide) with h31010 | h31010
                · rcases m.htr 1 4 5 (by decide) (by decide) with h31011 | h31011
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h31012 | h31012
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h31013 | h31013
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h31014 | h31014
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h31015 | h31015
                          · rcases h0bigk with h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c | h31016c
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [hlam, p31016_0]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h0, hlam, p31016_1]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h15532, hlam, p31016_0]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h18443, hlam, p31016_1]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h20697, hlam, p31016_1]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h22350, h30702, hc01, hc34, hlam, hphi, ht12, ht23, p31016_1]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [hlam, p31016_0]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h22350, hlam, p31016_0]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h30132, hlam, p31016_1]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h20697, h22350, h30702, hc01, hc34, hlam, hphi, ht12, ht23, p31016_1]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h30702, hc01, hc34, hlam, hphi, ht12, ht23, p31016_1]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h30702, hc02, hc34, hlam, hphi, ht23, p31016_1]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [hlam, p31016_0]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h30702, hlam, p31016_1]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h20697, h30702, hc01, hc34, hlam, hphi, ht12, ht23, p31016_1]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h30702, h30955, h31009, hc01, hc23, hlam, hphi, ht12, p31016_1]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h30701, h30702, h30955, h31009, h31013, h31015, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p31016_1]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h15532, h30702, h30955, h31009, hc01, hc23, hlam, hphi, ht12, p31016_1]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [hlam, p31016_0]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h20697, h30702, h30955, h31009, hc01, hc23, hlam, hphi, ht12, p31016_1]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h0, h30701, h31006, h31012, hc01, hc23, hlam, hphi, ht12, p31016_1]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h30701, hlam, p31016_1]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h30953, hlam, p31016_0]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [h30954, hlam, p31016_1]
                            · have p31016_0 := h31016c.1
                              have p31016_1 := h31016c.2.1
                              have p31016_2 := h31016c.2.2.1
                              have p31016_3 := h31016c.2.2.2
                              linarith only [hlam, p31016_0]
                          · linarith only [h30702, h30954, h31015, hlam]
                        · linarith only [h30132, h30701, h30954, h31014, hlam]
                      · linarith only [h22350, h30702, h30955, h31009, h31013, hc02, hc35, hlam, hphi, ht23]
                    · linarith only [h30955, h31009, h31012, hlam]
                  · linarith only [h18443, h22350, h30701, h30702, h30954, h30955, h31009, h31011, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h30702, h30953, h31009, h31010, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h31048 | h31048
                · rcases m.htr 1 4 5 (by decide) (by decide) with h31049 | h31049
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h31050 | h31050
                    · linarith only [h20697, h30955, h31008, h31009, h31050, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h20697, h30955, h31008, h31050, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h18443, h30701, h30954, h30955, h31049, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h15532, h30953, h31048, hlam]
            · linarith only [h0, h15532, h22350, h30701, h31008, hc01, hc13, hlam, hphi]
      · linarith only [h22350, h30701, h30702, h30954, hlam]
    · linarith only [h22350, h30701, h30953, hlam]

end R2N4
