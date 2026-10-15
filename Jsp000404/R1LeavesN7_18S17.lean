import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9598000 in
set_option maxHeartbeats 9598000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s7_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5743 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h5744 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h5745 | h5745
  · rcases m.htr 0 2 3 (by decide) (by decide) with h5746 | h5746
    · rcases m.htr 0 2 4 (by decide) (by decide) with h5747 | h5747
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5748 | h5748
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5749 | h5749
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5750 | h5750
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5751 | h5751
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5752 | h5752
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5753 | h5753
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5754 | h5754
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5755 | h5755
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5756 | h5756
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5757 | h5757
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5758 | h5758
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5759 | h5759
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5760 | h5760
                                · linarith only [h0, h5743, h5752, h5757, h5760, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h0, h5743, h5753, h5755, h5759, h5760, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5763 | h5763
                                · linarith only [h0, h5743, h5749, h5759, h5763, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases h0bigk with h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [hlam, p5765_0]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h0, hlam, p5765_1]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5765_1]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5765_1]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p5765_1]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h5743, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p5765_1]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [hlam, p5765_0]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h0, h5743, h5752, h5758, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p5765_1]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h0, h5751, h5759, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p5765_1]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h0, h5751, h5759, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5765_1]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h5743, hlam, p5765_1]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h5746, hlam, p5765_1]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [hlam, p5765_0]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h5743, h5751, h5759, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p5765_1]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h0, h5743, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p5765_1]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h5744, hlam, p5765_0]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h5747, hlam, p5765_0]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h5749, hlam, p5765_0]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [hlam, p5765_0]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h0, h5744, h5748, h5758, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p5765_1]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h5745, hlam, p5765_0]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h5748, hlam, p5765_1]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h5750, hlam, p5765_0]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [h5751, hlam, p5765_1]
                                  · have p5765_0 := h5765c.1
                                    have p5765_1 := h5765c.2.1
                                    have p5765_2 := h5765c.2.2.1
                                    have p5765_3 := h5765c.2.2.2
                                    linarith only [hlam, p5765_0]
                            · linarith only [h0, h5743, h5750, h5757, h5758, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h5743, h5755, h5757, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h5743, h5750, h5755, h5756, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5794 | h5794
                        · linarith only [h0, h5743, h5749, h5755, h5794, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5796 | h5796
                          · linarith only [h5752, h5755, h5796, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5798 | h5798
                            · linarith only [h5752, h5794, h5798, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5800 | h5800
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5801 | h5801
                                · rcases h0bigk with h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c | h5802c
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [hlam, p5802_0]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h0, hlam, p5802_1]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5802_1]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5802_1]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h0, h5750, h5752, h5794, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5802_1]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p5802_1]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [hlam, p5802_0]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h0, h5749, h5753, h5755, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5802_1]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h0, h5751, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5802_1]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h0, h5750, h5752, h5794, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5802_1]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h5743, hlam, p5802_1]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h5746, hlam, p5802_1]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [hlam, p5802_0]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h5743, h5751, hc01, hc45, hlam, hphi, ht0b, ht5b, p5802_1]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h0, h5743, h5750, h5752, h5794, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5802_1]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h5744, hlam, p5802_0]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h5747, hlam, p5802_0]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h5749, hlam, p5802_0]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [hlam, p5802_0]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h5750, h5752, h5794, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5802_1]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h5745, hlam, p5802_0]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h5748, hlam, p5802_1]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h5750, hlam, p5802_0]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [h5751, hlam, p5802_1]
                                  · have p5802_0 := h5802c.1
                                    have p5802_1 := h5802c.2.1
                                    have p5802_2 := h5802c.2.2.1
                                    have p5802_3 := h5802c.2.2.2
                                    linarith only [hlam, p5802_0]
                                · linarith only [h0, h5744, h5752, h5753, h5755, h5800, h5801, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5829 | h5829
                                · linarith only [h0, h5743, h5749, h5800, h5829, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h5743, h5749, h5751, h5752, h5755, h5829, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h5748, h5754, hlam]
                  · linarith only [h0, h5747, h5753, hlam]
                · linarith only [h0, h5746, h5752, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5835 | h5835
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5836 | h5836
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5837 | h5837
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5838 | h5838
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5839 | h5839
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5840 | h5840
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5841 | h5841
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5842 | h5842
                              · linarith only [h0, h5744, h5751, h5836, h5842, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5844 | h5844
                                · linarith only [h5744, h5751, h5836, h5840, h5844, hlam]
                                · rcases h0bigk with h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c | h5846c
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [hlam, p5846_0]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h0, hlam, p5846_1]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h0, h5743, h5835, h5841, h5844, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5846_1]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h0, h5744, h5836, h5840, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5846_1]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h0, h5744, h5751, h5836, h5840, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5846_1]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p5846_1]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [hlam, p5846_0]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h0, h5743, h5835, h5841, h5844, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5846_1]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    rcases p5846_3 (m.d 0 1) (by simp) with h5855 | h5855
                                    · linarith only [h0, h5855, hlam]
                                    · linarith only [h5744, h5855, hlam]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    rcases p5846_3 (m.d 0 1) (by simp) with h5858 | h5858
                                    · linarith only [h0, h5858, hlam]
                                    · linarith only [h5745, h5858, hlam]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h5743, hlam, p5846_1]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h5746, hlam, p5846_1]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [hlam, p5846_0]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h0, h5743, h5744, h5836, h5840, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5846_1]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h0, h5743, h5744, h5751, h5836, h5840, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5846_1]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h5744, hlam, p5846_0]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h5747, hlam, p5846_0]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h5749, hlam, p5846_0]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [hlam, p5846_0]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h5751, hlam, p5846_0]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h5745, hlam, p5846_0]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h5748, hlam, p5846_1]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h5750, hlam, p5846_0]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [h0, h5744, h5745, h5836, h5840, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5846_1]
                                  · have p5846_0 := h5846c.1
                                    have p5846_1 := h5846c.2.1
                                    have p5846_2 := h5846c.2.2.1
                                    have p5846_3 := h5846c.2.2.2
                                    linarith only [hlam, p5846_0]
                            · linarith only [h0, h5743, h5839, h5841, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h0, h5743, h5838, h5840, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h5743, h5750, h5838, h5839, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5879 | h5879
                        · linarith only [h0, h5743, h5749, h5838, h5879, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5881 | h5881
                          · linarith only [h5835, h5838, h5881, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5883 | h5883
                            · linarith only [h0, h5743, h5749, h5835, h5837, h5838, h5879, h5883, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5885 | h5885
                              · linarith only [h5747, h5751, h5885, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5887 | h5887
                                · linarith only [h0, h5743, h5749, h5750, h5751, h5835, h5879, h5887, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · rcases h0bigk with h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c | h5889c
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [hlam, p5889_0]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h0, hlam, p5889_1]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5889_1]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5889_1]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h0, h5744, h5751, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p5889_1]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p5889_1]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [hlam, p5889_0]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h0, h5750, h5838, h5887, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p5889_1]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h0, h5749, h5835, h5838, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5889_1]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h0, h5750, h5835, h5838, h5887, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5889_1]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h5743, hlam, p5889_1]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h5746, hlam, p5889_1]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [hlam, p5889_0]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h5743, h5749, h5835, h5838, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5889_1]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h0, h5743, h5750, h5835, h5838, h5887, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5889_1]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h5744, hlam, p5889_0]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h5747, hlam, p5889_0]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h5749, hlam, p5889_0]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [hlam, p5889_0]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h5751, hlam, p5889_0]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h5745, hlam, p5889_0]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h5748, hlam, p5889_1]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h5750, hlam, p5889_0]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [h5749, h5835, h5838, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5889_1]
                                  · have p5889_0 := h5889c.1
                                    have p5889_1 := h5889c.2.1
                                    have p5889_2 := h5889c.2.2.1
                                    have p5889_3 := h5889c.2.2.2
                                    linarith only [hlam, p5889_0]
                    · linarith only [h0, h5748, h5837, hlam]
                  · linarith only [h0, h5747, h5836, hlam]
                · linarith only [h0, h5746, h5835, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5918 | h5918
              · linarith only [h5749, h5750, h5918, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5920 | h5920
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5921 | h5921
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5922 | h5922
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5923 | h5923
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5924 | h5924
                        · linarith only [h0, h5743, h5750, h5924, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5926 | h5926
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5927 | h5927
                            · linarith only [h5743, h5750, h5920, h5927, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5929 | h5929
                              · linarith only [h0, h5744, h5918, h5921, h5929, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5931 | h5931
                                · linarith only [h5749, h5750, h5918, h5931, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                · rcases h0bigk with h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c | h5933c
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [hlam, p5933_0]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h0, hlam, p5933_1]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5933_1]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5933_1]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h0, h5750, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5933_1]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p5933_1]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [hlam, p5933_0]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h0, h5749, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5933_1]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    rcases p5933_3 (m.d 0 1) (by simp) with h5942 | h5942
                                    · linarith only [h0, h5942, hlam]
                                    · linarith only [h5744, h5942, hlam]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h0, h5743, h5750, h5920, h5926, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5933_1]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h5743, hlam, p5933_1]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h5746, hlam, p5933_1]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [hlam, p5933_0]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h0, h5743, h5744, h5921, h5926, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5933_1]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h5750, hlam, p5933_1]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h5744, hlam, p5933_0]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h5747, hlam, p5933_0]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h5749, hlam, p5933_0]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [hlam, p5933_0]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h5918, hlam, p5933_0]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h5745, hlam, p5933_0]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h5748, hlam, p5933_1]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h5743, h5920, h5926, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p5933_1]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [h0, h5744, h5745, h5921, h5926, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5933_1]
                                  · have p5933_0 := h5933c.1
                                    have p5933_1 := h5933c.2.1
                                    have p5933_2 := h5933c.2.2.1
                                    have p5933_3 := h5933c.2.2.2
                                    linarith only [hlam, p5933_0]
                          · linarith only [h5749, h5750, h5926, hc23, hc35, hlam, hphi]
                      · linarith only [h5749, h5750, h5923, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h5748, h5922, hlam]
                  · linarith only [h0, h5747, h5921, hlam]
                · linarith only [h0, h5746, h5920, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5966 | h5966
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5967 | h5967
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5968 | h5968
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5969 | h5969
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5970 | h5970
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5971 | h5971
                      · linarith only [h0, h5743, h5749, h5966, h5971, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5973 | h5973
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5974 | h5974
                          · linarith only [h5743, h5749, h5968, h5974, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5976 | h5976
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5977 | h5977
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5978 | h5978
                                · rcases h0bigk with h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [hlam, p5979_0]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h0, hlam, p5979_1]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h0, h5743, h5968, h5976, h5978, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5979_1]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h0, h5743, h5749, h5968, h5976, h5978, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5979_1]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p5979_1]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p5979_1]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [hlam, p5979_0]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h0, h5743, h5968, h5976, h5978, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5979_1]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h0, h5743, h5749, h5968, h5976, h5978, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5979_1]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    rcases p5979_3 (m.d 0 1) (by simp) with h5989 | h5989
                                    · linarith only [h0, h5989, hlam]
                                    · linarith only [h5745, h5989, hlam]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h5743, hlam, p5979_1]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h5746, hlam, p5979_1]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [hlam, p5979_0]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h5749, hlam, p5979_1]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h5745, h5749, h5970, h5976, h5978, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5979_1]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h5744, hlam, p5979_0]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h5747, hlam, p5979_0]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h5743, h5968, h5976, h5978, hc04, hc45, hlam, hphi, ht0b, ht5b, p5979_1]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [hlam, p5979_0]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h0, h5744, h5745, h5970, h5976, h5978, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5979_1]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h5745, hlam, p5979_0]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h5748, hlam, p5979_1]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h5966, hlam, p5979_0]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [h5967, hlam, p5979_1]
                                  · have p5979_0 := h5979c.1
                                    have p5979_1 := h5979c.2.1
                                    have p5979_2 := h5979c.2.2.1
                                    have p5979_3 := h5979c.2.2.2
                                    linarith only [hlam, p5979_0]
                                · linarith only [h5743, h5749, h5967, h5968, h5976, h5978, hc04, hc35, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h5744, h5967, h5974, h5976, h5977, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h5749, h5966, h5976, hc23, hc34, hlam, hphi]
                        · linarith only [h5749, h5966, h5973, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h5748, h5970, hlam]
                  · linarith only [h0, h5747, h5969, hlam]
                · linarith only [h0, h5746, h5968, hlam]
              · linarith only [h5749, h5966, h5967, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6015 | h6015
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6016 | h6016
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6017 | h6017
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6018 | h6018
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6019 | h6019
                      · linarith only [h0, h5743, h5749, h6019, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6021 | h6021
                        · linarith only [h5743, h5966, h6021, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6023 | h6023
                          · linarith only [h5746, h5749, h6023, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6025 | h6025
                            · linarith only [h5743, h5966, h6016, h6025, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6027 | h6027
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6028 | h6028
                                · rcases h0bigk with h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c | h6029c
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [hlam, p6029_0]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h0, hlam, p6029_1]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6029_1]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h0, h5743, h5966, h6015, h6016, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6029_1]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h0, h5743, h5966, h6016, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6029_1]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6029_1]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [hlam, p6029_0]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    rcases p6029_3 (m.d 0 1) (by simp) with h6037 | h6037
                                    · linarith only [h0, h6037, hlam]
                                    · linarith only [h5743, h6037, hlam]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h0, h5744, h6017, h6027, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6029_1]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    rcases p6029_3 (m.d 0 1) (by simp) with h6041 | h6041
                                    · linarith only [h0, h6041, hlam]
                                    · linarith only [h5745, h6041, hlam]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h5743, hlam, p6029_1]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h5746, hlam, p6029_1]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [hlam, p6029_0]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h5749, hlam, p6029_1]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h5966, hlam, p6029_1]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h5744, hlam, p6029_0]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h5747, hlam, p6029_0]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h0, h5743, h5744, h6016, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6029_1]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [hlam, p6029_0]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h5743, h5749, h5966, h6016, hc23, hc34, hlam, hphi, p6029_1]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h5745, hlam, p6029_0]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h5748, hlam, p6029_1]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h0, h5743, h5745, h6016, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6029_1]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [h6015, hlam, p6029_1]
                                  · have p6029_0 := h6029c.1
                                    have p6029_1 := h6029c.2.1
                                    have p6029_2 := h6029c.2.2.1
                                    have p6029_3 := h6029c.2.2.2
                                    linarith only [hlam, p6029_0]
                                · linarith only [h0, h5744, h6017, h6027, h6028, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6060 | h6060
                                · rcases h0bigk with h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c | h6061c
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [hlam, p6061_0]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h0, hlam, p6061_1]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h0, h5743, h6016, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6061_1]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6061_1]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h0, h6015, h6023, h6027, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6061_1]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6061_1]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [hlam, p6061_0]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    rcases p6061_3 (m.d 0 1) (by simp) with h6069 | h6069
                                    · linarith only [h0, h6069, hlam]
                                    · linarith only [h5743, h6069, hlam]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h0, h6015, h6023, h6027, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6061_1]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h0, h6015, h6023, h6027, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6061_1]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h5743, hlam, p6061_1]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h5746, hlam, p6061_1]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [hlam, p6061_0]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h5749, hlam, p6061_1]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h5966, hlam, p6061_1]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h5744, hlam, p6061_0]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h5747, hlam, p6061_0]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h5743, h5749, h6016, hc23, hc34, hlam, hphi, p6061_1]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [hlam, p6061_0]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h0, h5744, h6015, h6023, h6027, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6061_1]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h5745, hlam, p6061_0]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h5748, hlam, p6061_1]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h5743, h5966, h6016, hc23, hc35, hlam, hphi, p6061_1]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [h6015, hlam, p6061_1]
                                  · have p6061_0 := h6061c.1
                                    have p6061_1 := h6061c.2.1
                                    have p6061_2 := h6061c.2.2.1
                                    have p6061_3 := h6061c.2.2.2
                                    linarith only [hlam, p6061_0]
                                · linarith only [h5749, h6015, h6060, hlam]
                    · linarith only [h0, h5748, h6018, hlam]
                  · linarith only [h0, h5747, h6017, hlam]
                · linarith only [h0, h5746, h6016, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6093 | h6093
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6094 | h6094
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6095 | h6095
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6096 | h6096
                      · linarith only [h5743, h5749, h6096, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6098 | h6098
                        · linarith only [h5743, h5966, h6098, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6100 | h6100
                          · linarith only [h5743, h5749, h6093, h6100, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6102 | h6102
                            · linarith only [h5743, h5966, h6093, h6102, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6104 | h6104
                              · linarith only [h0, h5744, h6015, h6094, h6104, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6106 | h6106
                                · rcases h0bigk with h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c | h6107c
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [hlam, p6107_0]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [h0, hlam, p6107_1]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [h0, h5743, h6093, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6107_1]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6107_1]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [h0, h5744, h6015, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p6107_1]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6107_1]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [hlam, p6107_0]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    rcases p6107_3 (m.d 0 1) (by simp) with h6115 | h6115
                                    · linarith only [h0, h6115, hlam]
                                    · linarith only [h5743, h6115, hlam]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    rcases p6107_3 (m.d 0 1) (by simp) with h6118 | h6118
                                    · linarith only [h0, h6118, hlam]
                                    · linarith only [h5744, h6118, hlam]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    rcases p6107_3 (m.d 0 1) (by simp) with h6121 | h6121
                                    · linarith only [h0, h6121, hlam]
                                    · linarith only [h5745, h6121, hlam]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [h5743, hlam, p6107_1]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [h5746, hlam, p6107_1]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [hlam, p6107_0]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [h5749, hlam, p6107_1]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [h5966, hlam, p6107_1]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [h5744, hlam, p6107_0]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [h5747, hlam, p6107_0]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [h0, h5743, h5744, h6093, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6107_1]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [hlam, p6107_0]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [h6015, hlam, p6107_0]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [h5745, hlam, p6107_0]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [h5748, hlam, p6107_1]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [h0, h5743, h5745, h6093, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6107_1]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [h0, h5745, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6107_1]
                                  · have p6107_0 := h6107c.1
                                    have p6107_1 := h6107c.2.1
                                    have p6107_2 := h6107c.2.2.1
                                    have p6107_3 := h6107c.2.2.2
                                    linarith only [hlam, p6107_0]
                                · rcases h0bigk with h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c | h6139c
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [hlam, p6139_0]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [h0, hlam, p6139_1]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [h0, h5743, h6093, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6139_1]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [h0, h5744, h6093, h6096, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6139_1]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6139_1]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6139_1]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [hlam, p6139_0]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    rcases p6139_3 (m.d 0 1) (by simp) with h6147 | h6147
                                    · linarith only [h0, h6147, hlam]
                                    · linarith only [h5743, h6147, hlam]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    rcases p6139_3 (m.d 0 1) (by simp) with h6150 | h6150
                                    · linarith only [h0, h6150, hlam]
                                    · linarith only [h5744, h6150, hlam]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    rcases p6139_3 (m.d 0 1) (by simp) with h6153 | h6153
                                    · linarith only [h0, h6153, hlam]
                                    · linarith only [h5745, h6153, hlam]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [h5743, hlam, p6139_1]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [h5746, hlam, p6139_1]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [hlam, p6139_0]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [h5749, hlam, p6139_1]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [h5966, hlam, p6139_1]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [h5744, hlam, p6139_0]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [h5747, hlam, p6139_0]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [h0, h5743, h5744, h6093, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6139_1]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [hlam, p6139_0]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [h6015, hlam, p6139_0]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [h5745, hlam, p6139_0]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [h5748, hlam, p6139_1]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [h0, h5743, h5745, h6093, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6139_1]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [h5744, h5966, h6093, h6096, hc23, hc35, hlam, hphi, p6139_1]
                                  · have p6139_0 := h6139c.1
                                    have p6139_1 := h6139c.2.1
                                    have p6139_2 := h6139c.2.2.1
                                    have p6139_3 := h6139c.2.2.2
                                    linarith only [hlam, p6139_0]
                    · linarith only [h0, h5748, h6095, hlam]
                  · linarith only [h0, h5747, h6094, hlam]
                · linarith only [h0, h5746, h6093, hlam]
        · linarith only [h0, h5745, h5748, hlam]
      · linarith only [h0, h5744, h5747, hlam]
    · linarith only [h0, h5743, h5746, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6177 | h6177
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6178 | h6178
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6179 | h6179
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6180 | h6180
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6181 | h6181
            · linarith only [h5743, h5745, h6181, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6183 | h6183
              · linarith only [h5743, h5745, h6180, h6183, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6185 | h6185
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6186 | h6186
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6187 | h6187
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6188 | h6188
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6189 | h6189
                        · linarith only [h5743, h5745, h6181, h6187, h6189, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6191 | h6191
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6192 | h6192
                            · linarith only [h5743, h5745, h6185, h6189, h6192, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6194 | h6194
                              · linarith only [h5744, h5745, h6183, h6186, h6189, h6194, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6196 | h6196
                                · linarith only [h5743, h5745, h6183, h6185, h6191, h6196, hlam]
                                · linarith only [h5743, h5745, h6185, h6189, h6191, h6196, hc34, hc45, hlam, hphi]
                          · linarith only [h5743, h5745, h6188, h6189, h6191, hc23, hc35, hlam, hphi]
                      · linarith only [h6180, h6181, h6188, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h6179, h6187, hlam]
                  · linarith only [h0, h6178, h6186, hlam]
                · linarith only [h0, h6177, h6185, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6204 | h6204
            · linarith only [h5744, h5745, h6180, h6204, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6206 | h6206
              · linarith only [h5744, h5745, h6206, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6208 | h6208
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6209 | h6209
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6210 | h6210
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6211 | h6211
                      · linarith only [h5743, h5745, h6180, h6210, h6211, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6213 | h6213
                        · linarith only [h5743, h5745, h6204, h6213, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6215 | h6215
                          · linarith only [h6177, h6180, h6215, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6217 | h6217
                            · linarith only [h5743, h5745, h6208, h6213, h6217, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6219 | h6219
                              · linarith only [h5744, h5745, h6206, h6209, h6213, h6219, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6221 | h6221
                                · rcases h0bigk with h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c | h6222c
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [hlam, p6222_0]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h0, hlam, p6222_1]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h5745, h6206, h6221, hc03, hc34, hlam, hphi, p6222_1]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h5745, h6206, h6221, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p6222_1]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h5745, hlam, p6222_1]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6222_1]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [hlam, p6222_0]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    rcases p6222_3 (m.d 0 1) (by simp) with h6230 | h6230
                                    · linarith only [h0, h6230, hlam]
                                    · linarith only [h5743, h6230, hlam]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    rcases p6222_3 (m.d 0 1) (by simp) with h6233 | h6233
                                    · linarith only [h0, h6233, hlam]
                                    · linarith only [h5744, h6233, hlam]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h0, h5744, h5745, h6208, h6211, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6222_1]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h5743, hlam, p6222_1]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h6177, hlam, p6222_1]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [hlam, p6222_0]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h6180, hlam, p6222_1]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h6204, hlam, p6222_1]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h5744, hlam, p6222_0]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h6178, hlam, p6222_0]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h5743, h5744, h5745, h6208, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6222_1]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [hlam, p6222_0]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h6206, hlam, p6222_0]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h5743, h6208, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6222_1]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h6179, hlam, p6222_1]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h5743, h5745, h6208, h6213, hc23, hc35, hlam, hphi, p6222_1]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [h6206, h6221, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p6222_1]
                                  · have p6222_0 := h6222c.1
                                    have p6222_1 := h6222c.2.1
                                    have p6222_2 := h6222c.2.2.1
                                    have p6222_3 := h6222c.2.2.2
                                    linarith only [hlam, p6222_0]
                                · rcases h0bigk with h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [hlam, p6252_0]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h0, hlam, p6252_1]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h5743, h5745, h6208, h6213, h6221, hc23, hc45, hlam, hphi, ht34, p6252_1]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h5744, h5745, h6208, h6211, h6213, h6221, hc23, hc45, hlam, hphi, ht34, p6252_1]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h5745, hlam, p6252_1]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6252_1]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [hlam, p6252_0]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    rcases p6252_3 (m.d 0 1) (by simp) with h6260 | h6260
                                    · linarith only [h0, h6260, hlam]
                                    · linarith only [h5743, h6260, hlam]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    rcases p6252_3 (m.d 0 1) (by simp) with h6263 | h6263
                                    · linarith only [h0, h6263, hlam]
                                    · linarith only [h5744, h6263, hlam]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h0, h5744, h5745, h6208, h6211, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6252_1]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h5743, hlam, p6252_1]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h6177, hlam, p6252_1]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [hlam, p6252_0]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h6180, hlam, p6252_1]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h6204, hlam, p6252_1]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h5744, hlam, p6252_0]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h6178, hlam, p6252_0]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h0, h5743, h5744, h6208, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6252_1]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [hlam, p6252_0]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h6206, hlam, p6252_0]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h5743, h6208, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6252_1]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h6179, hlam, p6252_1]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h5743, h5745, h6208, h6213, h6221, hc23, hc45, hlam, hphi, ht34, p6252_1]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [h5745, h6213, h6221, hc04, hc45, hlam, hphi, p6252_1]
                                  · have p6252_0 := h6252c.1
                                    have p6252_1 := h6252c.2.1
                                    have p6252_2 := h6252c.2.2.1
                                    have p6252_3 := h6252c.2.2.2
                                    linarith only [hlam, p6252_0]
                    · linarith only [h0, h6179, h6210, hlam]
                  · linarith only [h0, h6178, h6209, hlam]
                · linarith only [h0, h6177, h6208, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6285 | h6285
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6286 | h6286
            · linarith only [h0, h5743, h6179, h6286, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6288 | h6288
              · linarith only [h0, h5744, h6179, h6288, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6290 | h6290
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6291 | h6291
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6292 | h6292
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6293 | h6293
                      · linarith only [h0, h5743, h6179, h6292, h6293, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h5743, h6179, h6285, h6292, h6293, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6296 | h6296
                      · linarith only [h0, h5743, h6292, h6296, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h6285, h6286, h6296, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h5743, h6178, h6285, h6291, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h6177, h6290, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6301 | h6301
            · linarith only [h5743, h5745, h6301, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6303 | h6303
              · linarith only [h0, h5744, h6179, h6303, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6305 | h6305
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6306 | h6306
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6307 | h6307
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6308 | h6308
                      · linarith only [h0, h5743, h6179, h6285, h6307, h6308, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6310 | h6310
                        · linarith only [h0, h5743, h6179, h6301, h6310, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6312 | h6312
                          · linarith only [h6177, h6179, h6285, h6307, h6312, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6314 | h6314
                            · linarith only [h0, h5744, h6179, h6305, h6307, h6308, h6310, h6314, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6316 | h6316
                              · linarith only [h6178, h6179, h6303, h6316, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6318 | h6318
                                · linarith only [h0, h5744, h6179, h6308, h6316, h6318, hc13, hc34, hlam, hphi]
                                · rcases h0bigk with h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h0, hlam, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h0, h5743, h6179, h6305, h6307, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h0, h6179, h6307, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h5745, hlam, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6179, h6307, hc01, hc12, hlam, hphi, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h5743, h6179, h6305, h6307, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h5744, h6179, h6306, h6307, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6179, hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h5743, hlam, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6177, hlam, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6285, hlam, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6301, hlam, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h5744, hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6178, hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h0, h5743, h5744, h6305, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6303, hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h5743, h6305, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6179, h6307, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h5743, h6179, h6305, h6307, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6179, h6307, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [hlam, p6320_0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6346 | h6346
                      · linarith only [h0, h5743, h6307, h6346, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6348 | h6348
                        · linarith only [h0, h5744, h6307, h6346, h6348, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6350 | h6350
                          · linarith only [h5743, h6285, h6305, h6350, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6352 | h6352
                            · linarith only [h0, h5744, h5745, h6305, h6307, h6346, h6348, h6352, hc05, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h5744, h6305, h6307, h6346, h6352, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h5744, h6178, h6179, h6306, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h6177, h6305, hlam]
      · linarith only [h0, h5744, h6178, hlam]
    · linarith only [h0, h5743, h6177, hlam]

end R2N4
