import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5896000 in
set_option maxHeartbeats 5896000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5743 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6852 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h7594 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h5743 := hg5743
  have h6852 := hg6852
  rcases m.htr 0 2 3 (by decide) (by decide) with h7595 | h7595
  · rcases m.htr 0 2 4 (by decide) (by decide) with h7596 | h7596
    · rcases m.htr 0 2 5 (by decide) (by decide) with h7597 | h7597
      · rcases m.htr 0 3 4 (by decide) (by decide) with h7598 | h7598
        · rcases m.htr 0 3 5 (by decide) (by decide) with h7599 | h7599
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7600 | h7600
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7601 | h7601
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7602 | h7602
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7603 | h7603
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7604 | h7604
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7605 | h7605
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7606 | h7606
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7607 | h7607
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7608 | h7608
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7609 | h7609
                              · rcases h0bigk with h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c | h7610c
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [hlam, p7610_0]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [h0, hlam, p7610_1]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [h5743, hlam, p7610_0]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [h6852, hlam, p7610_1]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [h6852, h7604, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p7610_1]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p7610_1]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [hlam, p7610_0]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [h0, h7595, h7606, h7609, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7610_1]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [h0, h6852, h7594, h7603, h7607, h7609, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7610_1]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  rcases p7610_3 (m.d 0 1) (by simp) with h7620 | h7620
                                  · linarith only [h0, h7620, hlam]
                                  · linarith only [h7594, h7620, hlam]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [h7594, h7603, h7607, h7609, hc03, hc45, hlam, hphi, ht0b, ht5b, p7610_1]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [h7595, hlam, p7610_1]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [hlam, p7610_0]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [h5743, h6852, h7594, h7601, h7603, h7607, h7609, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7610_1]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  rcases p7610_3 (m.d 0 1) (by simp) with h7627 | h7627
                                  · linarith only [h5743, h7627, hlam]
                                  · linarith only [h7594, h7627, hlam]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [h7594, h7603, h7607, h7609, hc04, hc45, hlam, hphi, ht0b, ht5b, p7610_1]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [h7596, hlam, p7610_0]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [h7598, hlam, p7610_0]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [hlam, p7610_0]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  rcases p7610_3 (m.d 0 1) (by simp) with h7634 | h7634
                                  · linarith only [h6852, h7634, hlam]
                                  · linarith only [h7594, h7634, hlam]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [h7594, hlam, p7610_0]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [h7597, hlam, p7610_1]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [h7599, hlam, p7610_0]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [h7600, hlam, p7610_1]
                                · have p7610_0 := h7610c.1
                                  have p7610_1 := h7610c.2.1
                                  have p7610_2 := h7610c.2.2.1
                                  have p7610_3 := h7610c.2.2.2
                                  linarith only [hlam, p7610_0]
                              · rcases h0bigk with h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c | h7642c
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [hlam, p7642_0]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h0, hlam, p7642_1]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h5743, hlam, p7642_0]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h6852, hlam, p7642_1]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h6852, h7601, h7604, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7642_1]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p7642_1]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [hlam, p7642_0]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h0, h5743, h7594, h7603, h7608, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7642_1]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h0, h6852, h7594, h7603, h7608, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7642_1]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h0, h7600, h7609, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7642_1]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h7594, h7603, h7607, h7609, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7642_1]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h7595, hlam, p7642_1]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [hlam, p7642_0]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h5743, h6852, h7594, h7601, h7603, h7607, h7609, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7642_1]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h5743, h7600, h7601, h7609, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7642_1]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h7594, h7603, h7607, h7609, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p7642_1]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h7596, hlam, p7642_0]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h7598, hlam, p7642_0]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [hlam, p7642_0]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h6852, h7600, h7601, h7604, h7609, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7642_1]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h7594, hlam, p7642_0]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h7597, hlam, p7642_1]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h7599, hlam, p7642_0]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [h7600, hlam, p7642_1]
                                · have p7642_0 := h7642c.1
                                  have p7642_1 := h7642c.2.1
                                  have p7642_2 := h7642c.2.2.1
                                  have p7642_3 := h7642c.2.2.2
                                  linarith only [hlam, p7642_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7668 | h7668
                              · linarith only [h7606, h7608, h7668, hlam]
                              · rcases h0bigk with h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c | h7670c
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [hlam, p7670_0]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h0, hlam, p7670_1]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h5743, hlam, p7670_0]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h6852, hlam, p7670_1]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h7600, h7606, h7608, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7670_1]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p7670_1]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [hlam, p7670_0]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h0, h5743, hc01, hc12, hlam, hphi, p7670_1]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h0, h6852, h7594, h7600, h7606, h7608, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7670_1]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h0, h7600, h7606, h7608, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7670_1]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h7594, h7600, h7606, h7608, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7670_1]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h7595, hlam, p7670_1]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [hlam, p7670_0]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h5743, h6852, h7594, h7600, h7601, h7606, h7608, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7670_1]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h5743, h7600, h7601, h7606, h7608, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7670_1]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h7594, h7600, h7606, h7608, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p7670_1]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h7596, hlam, p7670_0]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h7598, hlam, p7670_0]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [hlam, p7670_0]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h6852, h7600, h7601, h7604, h7606, h7608, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7670_1]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h7594, hlam, p7670_0]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h7597, hlam, p7670_1]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h7599, hlam, p7670_0]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [h7600, hlam, p7670_1]
                                · have p7670_0 := h7670c.1
                                  have p7670_1 := h7670c.2.1
                                  have p7670_2 := h7670c.2.2.1
                                  have p7670_3 := h7670c.2.2.2
                                  linarith only [hlam, p7670_0]
                          · linarith only [h6852, h7594, h7601, h7604, h7605, h7606, h7607, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7697 | h7697
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7698 | h7698
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7699 | h7699
                              · rcases h0bigk with h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c | h7700c
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [hlam, p7700_0]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [h0, hlam, p7700_1]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [h5743, hlam, p7700_0]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [h6852, hlam, p7700_1]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [h6852, h7601, h7604, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7700_1]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p7700_1]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [hlam, p7700_0]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [h0, h5743, h7594, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p7700_1]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [h0, h6852, h7594, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p7700_1]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  rcases p7700_3 (m.d 0 1) (by simp) with h7710 | h7710
                                  · linarith only [h0, h7710, hlam]
                                  · linarith only [h7594, h7710, hlam]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [h7594, h7603, h7697, h7699, hc03, hc45, hlam, hphi, ht0b, ht5b, p7700_1]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [h7595, hlam, p7700_1]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [hlam, p7700_0]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [h5743, h7598, h7601, h7606, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7700_1]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  rcases p7700_3 (m.d 0 1) (by simp) with h7717 | h7717
                                  · linarith only [h5743, h7717, hlam]
                                  · linarith only [h7594, h7717, hlam]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [h7594, h7603, h7697, h7699, hc04, hc45, hlam, hphi, ht0b, ht5b, p7700_1]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [h7596, hlam, p7700_0]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [h7598, hlam, p7700_0]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [hlam, p7700_0]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  rcases p7700_3 (m.d 0 1) (by simp) with h7724 | h7724
                                  · linarith only [h6852, h7724, hlam]
                                  · linarith only [h7594, h7724, hlam]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [h7594, hlam, p7700_0]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [h7597, hlam, p7700_1]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [h7599, hlam, p7700_0]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [h7600, hlam, p7700_1]
                                · have p7700_0 := h7700c.1
                                  have p7700_1 := h7700c.2.1
                                  have p7700_2 := h7700c.2.2.1
                                  have p7700_3 := h7700c.2.2.2
                                  linarith only [hlam, p7700_0]
                              · linarith only [h6852, h7600, h7601, h7604, h7606, h7697, h7699, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h7606, h7697, h7698, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7734 | h7734
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7735 | h7735
                              · rcases h0bigk with h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c | h7736c
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [hlam, p7736_0]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h0, hlam, p7736_1]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h5743, hlam, p7736_0]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h6852, hlam, p7736_1]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h6852, h7601, h7604, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7736_1]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p7736_1]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [hlam, p7736_0]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h0, h7598, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7736_1]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h0, h6852, h7594, h7605, h7697, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7736_1]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h0, h7594, h7605, h7697, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7736_1]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h7594, h7605, h7697, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7736_1]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h7595, hlam, p7736_1]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [hlam, p7736_0]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h5743, h6852, h7594, h7601, h7605, h7697, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7736_1]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h5743, h7594, h7601, h7605, h7697, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7736_1]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h7594, h7605, h7697, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7736_1]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h7596, hlam, p7736_0]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h7598, hlam, p7736_0]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [hlam, p7736_0]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h6852, h7594, h7601, h7604, h7605, h7697, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7736_1]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h7594, hlam, p7736_0]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h7597, hlam, p7736_1]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h7599, hlam, p7736_0]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [h7600, hlam, p7736_1]
                                · have p7736_0 := h7736c.1
                                  have p7736_1 := h7736c.2.1
                                  have p7736_2 := h7736c.2.2.1
                                  have p7736_3 := h7736c.2.2.2
                                  linarith only [hlam, p7736_0]
                              · linarith only [h0, h7596, h7606, h7734, h7735, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7763 | h7763
                              · rcases h0bigk with h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c | h7764c
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [hlam, p7764_0]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h0, hlam, p7764_1]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h5743, hlam, p7764_0]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h6852, hlam, p7764_1]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h7594, h7605, h7606, h7734, h7763, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7764_1]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p7764_1]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [hlam, p7764_0]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h0, h7598, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7764_1]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h0, h6852, h7594, h7605, h7606, h7734, h7763, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7764_1]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h0, h7594, h7605, h7606, h7734, h7763, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7764_1]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h7594, h7605, h7606, h7734, h7763, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7764_1]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h7595, hlam, p7764_1]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [hlam, p7764_0]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h5743, h6852, h7594, h7601, h7605, h7606, h7734, h7763, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7764_1]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h5743, h7594, h7601, h7605, h7606, h7734, h7763, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7764_1]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h7594, h7605, h7606, h7734, h7763, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7764_1]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h7596, hlam, p7764_0]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h7598, hlam, p7764_0]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [hlam, p7764_0]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h6852, h7594, h7601, h7604, h7605, h7606, h7734, h7763, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7764_1]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h7594, hlam, p7764_0]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h7597, hlam, p7764_1]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h7599, hlam, p7764_0]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [h7600, hlam, p7764_1]
                                · have p7764_0 := h7764c.1
                                  have p7764_1 := h7764c.2.1
                                  have p7764_2 := h7764c.2.2.1
                                  have p7764_3 := h7764c.2.2.2
                                  linarith only [hlam, p7764_0]
                              · rcases h0bigk with h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c | h7790c
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [hlam, p7790_0]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h0, hlam, p7790_1]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h5743, hlam, p7790_0]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h6852, hlam, p7790_1]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h6852, h7601, h7604, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7790_1]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p7790_1]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [hlam, p7790_0]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h0, h5743, h7594, h7605, h7697, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p7790_1]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h0, h6852, h7594, h7605, h7697, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p7790_1]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h0, h7600, h7606, h7763, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7790_1]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h7594, h7600, h7606, h7763, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7790_1]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h7595, hlam, p7790_1]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [hlam, p7790_0]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h5743, h7600, h7601, h7606, h7763, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7790_1]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h5743, h7600, h7601, h7606, h7763, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7790_1]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h7594, h7600, h7606, h7763, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7790_1]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h7596, hlam, p7790_0]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h7598, hlam, p7790_0]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [hlam, p7790_0]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h6852, h7600, h7601, h7604, h7606, h7763, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7790_1]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h7594, hlam, p7790_0]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h7597, hlam, p7790_1]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h7599, hlam, p7790_0]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [h7600, hlam, p7790_1]
                                · have p7790_0 := h7790c.1
                                  have p7790_1 := h7790c.2.1
                                  have p7790_2 := h7790c.2.2.1
                                  have p7790_3 := h7790c.2.2.2
                                  linarith only [hlam, p7790_0]
                      · linarith only [h5743, h7599, h7605, hlam]
                    · linarith only [h5743, h7598, h7604, hlam]
                  · linarith only [h0, h7597, h7603, hlam]
                · linarith only [h0, h7596, h7602, hlam]
              · linarith only [h0, h7595, h7601, hlam]
            · linarith only [h6852, h7594, h7600, hlam]
          · linarith only [h5743, h7594, h7599, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h7823 | h7823
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7824 | h7824
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7825 | h7825
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7826 | h7826
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7827 | h7827
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7828 | h7828
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7829 | h7829
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7830 | h7830
                        · linarith only [h0, h5743, h7595, h7598, h7830, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7832 | h7832
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7833 | h7833
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7834 | h7834
                              · rcases h0bigk with h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c | h7835c
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [hlam, p7835_0]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h0, hlam, p7835_1]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h5743, hlam, p7835_0]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h6852, hlam, p7835_1]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h5743, h7598, h7828, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p7835_1]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p7835_1]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [hlam, p7835_0]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h0, h5743, h7594, h7827, h7832, h7834, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7835_1]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h0, h5743, h7594, h7598, h7827, h7832, h7834, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7835_1]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  rcases p7835_3 (m.d 0 1) (by simp) with h7845 | h7845
                                  · linarith only [h0, h7845, hlam]
                                  · linarith only [h7594, h7845, hlam]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h7594, h7827, h7832, h7834, hc03, hc45, hlam, hphi, ht0b, ht5b, p7835_1]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h7595, hlam, p7835_1]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [hlam, p7835_0]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h7598, hlam, p7835_1]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h7594, h7598, h7825, h7827, h7828, h7832, h7834, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7835_1]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h7594, h7598, h7825, h7827, h7828, h7832, h7834, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7835_1]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h7596, hlam, p7835_0]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h7598, h7825, h7828, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7835_1]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [hlam, p7835_0]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h7594, h7598, h7825, h7827, h7828, h7832, h7834, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7835_1]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h7594, hlam, p7835_0]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h7597, hlam, p7835_1]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h7823, hlam, p7835_0]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [h7824, hlam, p7835_1]
                                · have p7835_0 := h7835c.1
                                  have p7835_1 := h7835c.2.1
                                  have p7835_2 := h7835c.2.2.1
                                  have p7835_3 := h7835c.2.2.2
                                  linarith only [hlam, p7835_0]
                              · linarith only [h7598, h7824, h7834, hlam]
                            · linarith only [h5743, h7594, h7598, h7824, h7825, h7828, h7830, h7832, h7833, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h7598, h7823, h7825, h7828, h7832, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h7598, h7823, h7828, h7829, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7867 | h7867
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7868 | h7868
                        · linarith only [h5743, h7594, h7827, h7828, h7868, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7870 | h7870
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7871 | h7871
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7872 | h7872
                              · rcases h0bigk with h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c | h7873c
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [hlam, p7873_0]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h0, hlam, p7873_1]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h5743, hlam, p7873_0]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h6852, hlam, p7873_1]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h5743, h7828, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7873_1]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p7873_1]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [hlam, p7873_0]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h0, h5743, h7594, h7827, h7870, h7872, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7873_1]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h0, h6852, h7594, h7827, h7870, h7872, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7873_1]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  rcases p7873_3 (m.d 0 1) (by simp) with h7883 | h7883
                                  · linarith only [h0, h7883, hlam]
                                  · linarith only [h7594, h7883, hlam]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h7594, h7827, h7870, h7872, hc03, hc45, hlam, hphi, ht0b, ht5b, p7873_1]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h7595, hlam, p7873_1]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [hlam, p7873_0]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h7598, hlam, p7873_1]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h5743, h7594, h7827, h7828, h7870, h7872, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7873_1]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h6852, h7594, h7827, h7828, h7870, h7872, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7873_1]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h7596, hlam, p7873_0]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h6852, h7828, hc03, hc34, hlam, hphi, p7873_1]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [hlam, p7873_0]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  rcases p7873_3 (m.d 0 1) (by simp) with h7895 | h7895
                                  · linarith only [h6852, h7895, hlam]
                                  · linarith only [h7594, h7895, hlam]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h7594, hlam, p7873_0]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h7597, hlam, p7873_1]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h7823, hlam, p7873_0]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [h7824, hlam, p7873_1]
                                · have p7873_0 := h7873c.1
                                  have p7873_1 := h7873c.2.1
                                  have p7873_2 := h7873c.2.2.1
                                  have p7873_3 := h7873c.2.2.2
                                  linarith only [hlam, p7873_0]
                              · linarith only [h5743, h7828, h7872, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h5743, h7594, h7824, h7828, h7868, h7870, h7871, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h5743, h7823, h7828, h7870, hc23, hc34, hlam, hphi]
                      · linarith only [h5743, h7594, h7823, h7867, hlam]
                  · linarith only [h0, h7597, h7827, hlam]
                · linarith only [h0, h7596, h7826, hlam]
              · linarith only [h0, h7595, h7825, hlam]
            · linarith only [h5743, h7594, h7598, h7824, hlam]
          · linarith only [h5743, h7594, h7823, hlam]
      · linarith only [h0, h7594, h7597, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h7913 | h7913
      · rcases m.htr 0 3 4 (by decide) (by decide) with h7914 | h7914
        · linarith only [h7595, h7596, h7914, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h7916 | h7916
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7917 | h7917
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7918 | h7918
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7919 | h7919
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7920 | h7920
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7921 | h7921
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7922 | h7922
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7923 | h7923
                        · linarith only [h5743, h7595, h7596, h7914, h7919, h7923, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7925 | h7925
                          · linarith only [h7595, h7596, h7918, h7921, h7923, h7925, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h7595, h7596, h7916, h7918, h7921, h7923, h7925, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h7595, h7596, h7916, h7921, h7922, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7929 | h7929
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7930 | h7930
                        · linarith only [h6852, h7595, h7596, h7919, h7921, h7930, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7932 | h7932
                          · linarith only [h7595, h7596, h7919, h7932, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h7595, h7596, h7916, h7919, h7932, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h5743, h7594, h7595, h7596, h7916, h7919, h7920, h7929, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h7596, h7919, h7920, hc02, hc25, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7937 | h7937
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7938 | h7938
                    · linarith only [h5743, h7914, h7918, h7919, h7938, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7940 | h7940
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7941 | h7941
                        · linarith only [h0, h7595, h7919, h7938, h7941, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7943 | h7943
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7944 | h7944
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7945 | h7945
                              · rcases h0bigk with h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [hlam, p7946_0]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h0, hlam, p7946_1]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h5743, hlam, p7946_0]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h6852, hlam, p7946_1]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h5743, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p7946_1]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h0, h7919, h7941, hc01, hc34, hlam, hphi, ht12, ht23, p7946_1]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [hlam, p7946_0]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h0, h7919, h7941, hc03, hc34, hlam, hphi, p7946_1]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h7596, hlam, p7946_1]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h0, h7594, h7919, h7937, h7941, h7943, h7945, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7946_1]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h7594, h7937, h7943, h7945, hc03, hc45, hlam, hphi, ht0b, ht5b, p7946_1]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h7595, hlam, p7946_1]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [hlam, p7946_0]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h7914, hlam, p7946_1]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h0, h7594, h7595, h7919, h7937, h7941, h7943, h7945, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7946_1]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h7594, h7937, h7943, h7945, hc04, hc45, hlam, hphi, ht0b, ht5b, p7946_1]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h7596, h7941, hc02, hc34, hlam, hphi, ht23, p7946_1]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h7596, h7941, hc03, hc34, hlam, hphi, p7946_1]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [hlam, p7946_0]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  rcases p7946_3 (m.d 0 1) (by simp) with h7966 | h7966
                                  · linarith only [h6852, h7966, hlam]
                                  · linarith only [h7594, h7966, hlam]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h7594, hlam, p7946_0]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h7913, hlam, p7946_1]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h7916, hlam, p7946_0]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [h7917, hlam, p7946_1]
                                · have p7946_0 := h7946c.1
                                  have p7946_1 := h7946c.2.1
                                  have p7946_2 := h7946c.2.2.1
                                  have p7946_3 := h7946c.2.2.2
                                  linarith only [hlam, p7946_0]
                              · linarith only [h0, h7594, h7919, h7937, h7941, h7945, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h5743, h7594, h7917, h7918, h7919, h7937, h7943, h7944, hc05, hc35, hlam, hphi, ht0b, ht5b]
                          · linarith only [h5743, h7916, h7918, h7919, h7941, h7943, hc23, hc34, hlam, hphi]
                      · linarith only [h5743, h7594, h7916, h7940, hlam]
                  · linarith only [h0, h7913, h7937, hlam]
              · linarith only [h0, h7595, h7918, hlam]
            · linarith only [h0, h7594, h7596, h7917, hlam]
          · linarith only [h5743, h7594, h7916, hlam]
      · linarith only [h5743, h7594, h7595, h7913, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h7983 | h7983
    · rcases m.htr 0 2 5 (by decide) (by decide) with h7984 | h7984
      · rcases m.htr 0 3 4 (by decide) (by decide) with h7985 | h7985
        · rcases m.htr 0 3 5 (by decide) (by decide) with h7986 | h7986
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7987 | h7987
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7988 | h7988
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7989 | h7989
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7990 | h7990
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7991 | h7991
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7992 | h7992
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7993 | h7993
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7994 | h7994
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7995 | h7995
                            · linarith only [h7595, h7983, h7988, h7995, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h7595, h7983, h7987, h7988, h7995, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h7595, h7983, h7986, h7987, h7994, hc03, hc45, hlam, hphi, ht0b, ht5b]
                        · linarith only [h7595, h7985, h7993, hlam]
                      · linarith only [h5743, h7986, h7992, hlam]
                    · linarith only [h5743, h7594, h7595, h7983, h7985, h7990, h7991, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h6852, h7595, h7983, h7988, h7990, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h6852, h7594, h7595, h7983, h7988, h7989, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8004 | h8004
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8005 | h8005
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h8006 | h8006
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h8007 | h8007
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8008 | h8008
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8009 | h8009
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8010 | h8010
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8011 | h8011
                              · rcases h0bigk with h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [hlam, p8012_0]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h0, hlam, p8012_1]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h5743, hlam, p8012_0]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h6852, hlam, p8012_1]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h6852, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p8012_1]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h0, h7988, hc01, hc23, hlam, hphi, ht12, p8012_1]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [hlam, p8012_0]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h7595, hlam, p8012_0]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h0, h6852, h7594, h7988, h8005, h8009, h8011, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8012_1]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h0, h7594, h7988, h8005, h8009, h8011, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8012_1]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h7594, h7595, h8005, h8009, h8011, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8012_1]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h7595, hc02, hc23, hlam, hphi, p8012_1]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [hlam, p8012_0]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h6852, h7594, h7595, h8005, h8009, h8011, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8012_1]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  rcases p8012_3 (m.d 0 1) (by simp) with h8027 | h8027
                                  · linarith only [h5743, h8027, hlam]
                                  · linarith only [h7594, h8027, hlam]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h7594, h8005, h8009, h8011, hc04, hc45, hlam, hphi, ht0b, ht5b, p8012_1]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h7983, hlam, p8012_0]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h7985, hlam, p8012_0]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [hlam, p8012_0]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h0, h7594, h7983, h7988, h8005, h8009, h8011, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8012_1]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h7594, hlam, p8012_0]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h7984, hlam, p8012_1]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h7986, hlam, p8012_0]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [h7987, hlam, p8012_1]
                                · have p8012_0 := h8012c.1
                                  have p8012_1 := h8012c.2.1
                                  have p8012_2 := h8012c.2.2.1
                                  have p8012_3 := h8012c.2.2.2
                                  linarith only [hlam, p8012_0]
                              · linarith only [h0, h7983, h7988, h8010, h8011, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8041 | h8041
                              · linarith only [h8008, h8010, h8041, hlam]
                              · rcases h0bigk with h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c | h8043c
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [hlam, p8043_0]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h0, hlam, p8043_1]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h5743, hlam, p8043_0]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h6852, hlam, p8043_1]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h7987, h8008, h8010, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8043_1]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h0, h7988, hc01, hc23, hlam, hphi, ht12, p8043_1]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [hlam, p8043_0]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h7595, hlam, p8043_0]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h0, h7988, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8043_1]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h0, h7987, h7988, h8008, h8010, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8043_1]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h5743, h7594, h7988, h8005, h8008, h8010, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8043_1]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h5743, h7988, hc02, hc23, hlam, hphi, p8043_1]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [hlam, p8043_0]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h5743, h6852, h7594, h7988, h8005, h8008, h8010, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8043_1]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h5743, h7987, h7988, h8008, h8010, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8043_1]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h7594, h7983, h8005, h8008, h8010, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p8043_1]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h7983, hlam, p8043_0]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h7985, hlam, p8043_0]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [hlam, p8043_0]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h0, h7983, h7987, h7988, h8008, h8010, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8043_1]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h7594, hlam, p8043_0]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h7984, hlam, p8043_1]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h7986, hlam, p8043_0]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [h7987, hlam, p8043_1]
                                · have p8043_0 := h8043c.1
                                  have p8043_1 := h8043c.2.1
                                  have p8043_2 := h8043c.2.2.1
                                  have p8043_3 := h8043c.2.2.2
                                  linarith only [hlam, p8043_0]
                          · linarith only [h0, h7988, h8009, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h6852, h7594, h7988, h8004, h8005, h8008, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h5743, h7986, h8007, hlam]
                    · linarith only [h5743, h7985, h8006, hlam]
                  · linarith only [h0, h7984, h8005, hlam]
                · linarith only [h0, h7983, h8004, hlam]
            · linarith only [h6852, h7594, h7987, hlam]
          · linarith only [h5743, h7594, h7986, hlam]
        · linarith only [h7595, h7983, h7985, hlam]
      · linarith only [h6852, h7594, h7983, h7984, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h8079 | h8079
      · rcases m.htr 0 3 4 (by decide) (by decide) with h8080 | h8080
        · rcases m.htr 0 3 5 (by decide) (by decide) with h8081 | h8081
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8082 | h8082
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8083 | h8083
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8084 | h8084
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8085 | h8085
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h8086 | h8086
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h8087 | h8087
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8088 | h8088
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8089 | h8089
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8090 | h8090
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8091 | h8091
                              · rcases h0bigk with h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [hlam, p8092_0]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h0, hlam, p8092_1]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h5743, hlam, p8092_0]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h6852, hlam, p8092_1]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p8092_1]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h7983, h8084, hc01, hc14, hlam, hphi, p8092_1]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [hlam, p8092_0]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h7595, hlam, p8092_0]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h7983, hlam, p8092_1]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h7594, h7595, h8083, h8085, h8089, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8092_1]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h7594, h8085, h8089, hc03, hc35, hlam, hphi, ht0b, ht5b, p8092_1]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h0, h7594, h8085, h8089, hc03, hc35, hlam, hphi, ht0b, ht5b, p8092_1]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [hlam, p8092_0]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h7595, h8083, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p8092_1]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h7594, h7595, h8083, h8085, h8089, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8092_1]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h7594, h8085, h8089, hc04, hc35, hlam, hphi, ht0b, ht5b, p8092_1]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h0, h7594, h7983, h8085, h8089, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p8092_1]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h8080, hlam, p8092_0]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [hlam, p8092_0]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h7594, h7595, h8080, h8083, h8085, h8089, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8092_1]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h7594, hlam, p8092_0]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h8079, hlam, p8092_1]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h8081, hlam, p8092_0]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [h8082, hlam, p8092_1]
                                · have p8092_0 := h8092c.1
                                  have p8092_1 := h8092c.2.1
                                  have p8092_2 := h8092c.2.2.1
                                  have p8092_3 := h8092c.2.2.2
                                  linarith only [hlam, p8092_0]
                              · linarith only [h0, h7594, h7983, h8083, h8085, h8088, h8090, h8091, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h7595, h7983, h8080, h8082, h8083, h8090, hc01, hc12, hlam, hphi]
                          · linarith only [h7595, h8081, h8089, hlam]
                        · linarith only [h0, h7594, h7595, h8080, h8085, h8088, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h5743, h8081, h8087, hlam]
                    · linarith only [h5743, h7594, h8080, h8085, h8086, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h7595, h8083, h8085, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h7594, h7595, h8083, h8084, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8126 | h8126
                · linarith only [h0, h7594, h7983, h8083, h8126, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8128 | h8128
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h8129 | h8129
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h8130 | h8130
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8131 | h8131
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8132 | h8132
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8133 | h8133
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8134 | h8134
                              · rcases h0bigk with h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c | h8135c
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [hlam, p8135_0]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h0, hlam, p8135_1]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h5743, hlam, p8135_0]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h6852, hlam, p8135_1]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h0, h8126, h8131, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p8135_1]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h0, h8126, h8131, hc01, hc23, hlam, hphi, ht12, p8135_1]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [hlam, p8135_0]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h7595, hlam, p8135_0]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h7983, hlam, p8135_1]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h0, h7594, h8126, h8128, h8131, h8132, h8134, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8135_1]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h5743, h7594, h8083, h8128, h8132, h8134, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8135_1]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h5743, h8083, hc02, hc23, hlam, hphi, p8135_1]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [hlam, p8135_0]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h5743, h6852, h7594, h8083, h8128, h8132, h8134, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8135_1]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  rcases p8135_3 (m.d 0 1) (by simp) with h8150 | h8150
                                  · linarith only [h5743, h8150, hlam]
                                  · linarith only [h7594, h8150, hlam]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h7594, h8128, h8132, h8134, hc04, hc45, hlam, hphi, ht0b, ht5b, p8135_1]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h0, h6852, h7594, h8083, h8128, h8129, h8132, h8134, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8135_1]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h8080, hlam, p8135_0]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [hlam, p8135_0]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  rcases p8135_3 (m.d 0 1) (by simp) with h8157 | h8157
                                  · linarith only [h6852, h8157, hlam]
                                  · linarith only [h7594, h8157, hlam]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h7594, hlam, p8135_0]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h8079, hlam, p8135_1]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h8081, hlam, p8135_0]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [h8082, hlam, p8135_1]
                                · have p8135_0 := h8135c.1
                                  have p8135_1 := h8135c.2.1
                                  have p8135_2 := h8135c.2.2.1
                                  have p8135_3 := h8135c.2.2.2
                                  linarith only [hlam, p8135_0]
                              · linarith only [h0, h7594, h8126, h8128, h8131, h8133, h8134, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h7594, h8082, h8126, h8133, hc05, hc15, hlam, hphi, ht0b, ht5b]
                          · linarith only [h0, h7594, h8126, h8128, h8131, h8132, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h7594, h8083, h8128, h8131, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h5743, h8081, h8130, hlam]
                    · linarith only [h5743, h8080, h8129, hlam]
                  · linarith only [h0, h7594, h8079, h8128, hc02, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h7594, h7983, h8082, hlam]
          · linarith only [h0, h7594, h7983, h8080, h8081, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h8174 | h8174
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8175 | h8175
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8176 | h8176
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8177 | h8177
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8178 | h8178
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h8179 | h8179
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h8180 | h8180
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8181 | h8181
                        · linarith only [h0, h7594, h7595, h8080, h8176, h8178, h8181, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h7594, h7595, h8178, h8179, h8181, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h5743, h7594, h8174, h8178, h8180, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h8185 | h8185
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8186 | h8186
                        · linarith only [h8176, h8179, h8186, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8188 | h8188
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8189 | h8189
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8190 | h8190
                              · rcases h0bigk with h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c | h8191c
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [hlam, p8191_0]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h0, hlam, p8191_1]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h5743, hlam, p8191_0]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h6852, hlam, p8191_1]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p8191_1]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p8191_1]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [hlam, p8191_0]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h7595, hlam, p8191_0]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h7983, hlam, p8191_1]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h7594, h7595, h8176, h8178, h8179, h8188, h8190, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8191_1]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h7594, h7595, h8176, h8178, h8179, h8188, h8190, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8191_1]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h7595, h8176, h8179, hc02, hc34, hlam, hphi, ht23, p8191_1]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [hlam, p8191_0]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h8080, hlam, p8191_1]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h7594, h7595, h8176, h8178, h8179, h8188, h8190, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8191_1]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h7594, h7983, h8177, h8178, h8188, h8190, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8191_1]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h0, h7594, h7983, h8177, h8178, h8188, h8190, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8191_1]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h7983, h8177, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8191_1]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [hlam, p8191_0]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h7594, h7983, h8177, h8178, h8188, h8190, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8191_1]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h7594, hlam, p8191_0]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h8079, hlam, p8191_1]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h8174, hlam, p8191_0]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [h8175, hlam, p8191_1]
                                · have p8191_0 := h8191c.1
                                  have p8191_1 := h8191c.2.1
                                  have p8191_2 := h8191c.2.2.1
                                  have p8191_3 := h8191c.2.2.2
                                  linarith only [hlam, p8191_0]
                              · linarith only [h0, h7594, h7595, h8176, h8178, h8179, h8188, h8190, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h7983, h8175, h8189, hlam]
                          · linarith only [h0, h7594, h7595, h8174, h8178, h8188, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h7594, h7595, h8174, h8176, h8185, hlam]
                  · linarith only [h0, h8079, h8178, hlam]
                · linarith only [h0, h7594, h7595, h8176, h8177, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8223 | h8223
                · linarith only [h0, h7594, h7983, h8176, h8223, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8225 | h8225
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h8226 | h8226
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h8227 | h8227
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8228 | h8228
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8229 | h8229
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8230 | h8230
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8231 | h8231
                              · rcases h0bigk with h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c | h8232c
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [hlam, p8232_0]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h0, hlam, p8232_1]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h5743, hlam, p8232_0]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h6852, hlam, p8232_1]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h0, h7595, h8080, h8226, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p8232_1]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h7595, h8080, h8226, hc01, hc13, hlam, hphi, p8232_1]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [hlam, p8232_0]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h7595, hlam, p8232_0]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h7983, hlam, p8232_1]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h7594, h7595, h8080, h8225, h8226, h8229, h8231, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8232_1]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h7594, h8080, h8225, h8226, h8229, h8231, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8232_1]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h8080, h8226, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p8232_1]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [hlam, p8232_0]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h8080, hlam, p8232_1]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h7594, h8080, h8225, h8226, h8229, h8231, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8232_1]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h7594, h8225, h8229, h8231, hc04, hc45, hlam, hphi, ht0b, ht5b, p8232_1]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h0, h7594, h7983, h8225, h8228, h8229, h8231, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8232_1]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h8080, h8226, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8232_1]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [hlam, p8232_0]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h7594, h8080, h8225, h8226, h8229, h8231, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8232_1]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h7594, hlam, p8232_0]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h8079, hlam, p8232_1]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h8174, hlam, p8232_0]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [h8175, hlam, p8232_1]
                                · have p8232_0 := h8232c.1
                                  have p8232_1 := h8232c.2.1
                                  have p8232_2 := h8232c.2.2.1
                                  have p8232_3 := h8232c.2.2.2
                                  linarith only [hlam, p8232_0]
                              · linarith only [h8080, h8175, h8231, hlam]
                            · linarith only [h6852, h8175, h8223, h8230, hlam]
                          · linarith only [h5743, h8080, h8174, h8176, h8226, h8229, hc01, hc14, hlam, hphi]
                        · linarith only [h8176, h8226, h8228, hlam]
                      · linarith only [h0, h7594, h7595, h8080, h8225, h8226, h8227, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h8263 | h8263
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8264 | h8264
                        · linarith only [h0, h7594, h8176, h8225, h8226, h8264, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h7594, h8176, h8225, h8264, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h7594, h8174, h8176, h8225, h8263, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h8079, h8225, hlam]
            · linarith only [h5743, h7594, h8080, h8175, hlam]
          · linarith only [h0, h7594, h7595, h8174, hlam]
      · linarith only [h0, h7594, h8079, hlam]

end R2N4
