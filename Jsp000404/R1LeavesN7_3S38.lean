import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 16110000 in
set_option maxHeartbeats 16110000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s14_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16563 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16564 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h16565 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  rcases m.htr 0 2 4 (by decide) (by decide) with h16566 | h16566
  · rcases m.htr 0 2 5 (by decide) (by decide) with h16567 | h16567
    · rcases m.htr 0 3 4 (by decide) (by decide) with h16568 | h16568
      · rcases m.htr 0 3 5 (by decide) (by decide) with h16569 | h16569
        · rcases m.htr 0 4 5 (by decide) (by decide) with h16570 | h16570
          · rcases m.htr 1 2 3 (by decide) (by decide) with h16571 | h16571
            · rcases m.htr 1 2 4 (by decide) (by decide) with h16572 | h16572
              · rcases m.htr 1 2 5 (by decide) (by decide) with h16573 | h16573
                · rcases m.htr 1 3 4 (by decide) (by decide) with h16574 | h16574
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h16575 | h16575
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h16576 | h16576
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h16577 | h16577
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h16578 | h16578
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h16579 | h16579
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h16580 | h16580
                              · rcases h1bigk with h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c | h16581c
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [hlam, p16581_0]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [h0, hlam, p16581_0]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [h14799, hlam, p16581_0]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [h14799, h16571, h16574, h16580, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16581_1]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  rcases p16581_3 (m.d 0 1) (by simp) with h16586 | h16586
                                  · rcases p16581_3 (m.d 1 2) (by simp) with h16587 | h16587
                                    · rcases p16581_3 (m.d 1 3) (by simp) with h16588 | h16588
                                      · rcases p16581_3 (m.d 1 4) (by simp) with h16589 | h16589
                                        · linarith only [h16563, h16589, hlam]
                                        · linarith only [h16576, h16589, hlam]
                                      · linarith only [h16575, h16588, hlam]
                                    · linarith only [h16573, h16587, hlam]
                                  · linarith only [h16586, hlam, p16581_0]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [h16563, h16572, h16577, h16580, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16581_1]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [hlam, p16581_0]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [h14799, hc01, hc12, hlam, hphi, p16581_1]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  rcases p16581_3 (m.d 0 1) (by simp) with h16598 | h16598
                                  · linarith only [h0, h16598, hlam]
                                  · linarith only [h16563, h16598, hlam]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  rcases p16581_3 (m.d 0 1) (by simp) with h16601 | h16601
                                  · linarith only [h0, h16601, hlam]
                                  · linarith only [h16564, h16601, hlam]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [h16563, h16571, h16572, h16577, h16580, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16581_1]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [h16571, hlam, p16581_1]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [hlam, p16581_0]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  rcases p16581_3 (m.d 0 1) (by simp) with h16607 | h16607
                                  · linarith only [h14799, h16607, hlam]
                                  · linarith only [h16563, h16607, hlam]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  rcases p16581_3 (m.d 0 1) (by simp) with h16610 | h16610
                                  · linarith only [h14799, h16610, hlam]
                                  · linarith only [h16564, h16610, hlam]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [h16563, hlam, p16581_0]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [h16572, hlam, p16581_1]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [h16574, hlam, p16581_0]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [hlam, p16581_0]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [h0, h16563, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p16581_1]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [h16564, hlam, p16581_0]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [h16573, hlam, p16581_1]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [h16575, hlam, p16581_0]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [h16576, hlam, p16581_0]
                                · have p16581_0 := h16581c.1
                                  have p16581_1 := h16581c.2.1
                                  have p16581_2 := h16581c.2.2.1
                                  have p16581_3 := h16581c.2.2.2
                                  linarith only [hlam, p16581_0]
                              · linarith only [h14799, h16563, h16571, h16576, h16580, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h14799, h16563, h16571, h16576, h16579, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h14799, h16564, h16571, h16575, h16577, h16578, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h16626 | h16626
                          · linarith only [h14799, h16563, h16571, h16574, h16577, h16626, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h16628 | h16628
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h16629 | h16629
                              · rcases h1bigk with h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c | h16630c
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [hlam, p16630_0]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [h0, hlam, p16630_0]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [h14799, hlam, p16630_0]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [h14799, h16571, h16575, h16576, h16626, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16630_1]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [h14799, h16571, h16575, h16626, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16630_1]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [h16563, h16575, h16576, h16626, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16630_1]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [hlam, p16630_0]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [h14799, hc01, hc12, hlam, hphi, p16630_1]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  rcases p16630_3 (m.d 0 1) (by simp) with h16639 | h16639
                                  · linarith only [h0, h16639, hlam]
                                  · linarith only [h16563, h16639, hlam]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  rcases p16630_3 (m.d 0 1) (by simp) with h16642 | h16642
                                  · linarith only [h0, h16642, hlam]
                                  · linarith only [h16564, h16642, hlam]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [h16563, h16575, h16576, h16626, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16630_1]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [h16571, hlam, p16630_1]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [hlam, p16630_0]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  rcases p16630_3 (m.d 0 1) (by simp) with h16648 | h16648
                                  · linarith only [h14799, h16648, hlam]
                                  · linarith only [h16563, h16648, hlam]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  rcases p16630_3 (m.d 0 1) (by simp) with h16651 | h16651
                                  · linarith only [h14799, h16651, hlam]
                                  · linarith only [h16564, h16651, hlam]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [h16563, hlam, p16630_0]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [h16572, hlam, p16630_1]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [h16574, hlam, p16630_0]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [hlam, p16630_0]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [h16563, h16575, h16626, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16630_1]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [h16564, hlam, p16630_0]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [h16573, hlam, p16630_1]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [h16575, hlam, p16630_0]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [h16576, hlam, p16630_0]
                                · have p16630_0 := h16630c.1
                                  have p16630_1 := h16630c.2.1
                                  have p16630_2 := h16630c.2.2.1
                                  have p16630_3 := h16630c.2.2.2
                                  linarith only [hlam, p16630_0]
                              · linarith only [h14799, h16563, h16571, h16572, h16628, h16629, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h14799, h16563, h16571, h16576, h16577, h16628, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h16666 | h16666
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h16667 | h16667
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h16668 | h16668
                            · linarith only [h16572, h16576, h16668, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h16670 | h16670
                              · linarith only [h16574, h16576, h16670, hlam]
                              · rcases h1bigk with h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [hlam, p16672_0]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [h0, hlam, p16672_0]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [h14799, hlam, p16672_0]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  rcases p16672_3 (m.d 0 1) (by simp) with h16676 | h16676
                                  · rcases p16672_3 (m.d 1 2) (by simp) with h16677 | h16677
                                    · rcases p16672_3 (m.d 1 3) (by simp) with h16678 | h16678
                                      · rcases p16672_3 (m.d 1 4) (by simp) with h16679 | h16679
                                        · linarith only [h16679, hlam, p16672_0]
                                        · rcases p16672_3 (m.d 1 5) (by simp) with h16681 | h16681
                                          · linarith only [h16564, h16681, hlam]
                                          · linarith only [h16576, h16681, hlam]
                                      · linarith only [h16574, h16678, hlam]
                                    · linarith only [h16572, h16677, hlam]
                                  · linarith only [h16676, hlam, p16672_0]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  rcases p16672_3 (m.d 0 1) (by simp) with h16687 | h16687
                                  · rcases p16672_3 (m.d 1 2) (by simp) with h16688 | h16688
                                    · rcases p16672_3 (m.d 1 3) (by simp) with h16689 | h16689
                                      · rcases p16672_3 (m.d 1 4) (by simp) with h16690 | h16690
                                        · linarith only [h16563, h16690, hlam]
                                        · rcases p16672_3 (m.d 1 5) (by simp) with h16692 | h16692
                                          · linarith only [h16692, hlam, p16672_0]
                                          · rcases h3bigk with h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c | h16694c
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [hlam, p16694_0]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [h14799, hlam, p16694_1]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              rcases p16694_3 (m.d 0 3) (by simp) with h16697 | h16697
                                              · rcases p16694_3 (m.d 1 3) (by simp) with h16698 | h16698
                                                · rcases p16694_3 (m.d 2 3) (by simp) with h16699 | h16699
                                                  · linarith only [h16565, h16699, hlam]
                                                  · rcases p16694_3 (m.d 3 4) (by simp) with h16701 | h16701
                                                    · linarith only [h16568, h16701, hlam]
                                                    · rcases p16694_3 (m.d 3 5) (by simp) with h16703 | h16703
                                                      · linarith only [h16569, h16703, hlam]
                                                      · rcases h5bigk with h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c | h16705c
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [hlam, p16705_0]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h14799, h16563, h16570, h16571, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p16705_1]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h14799, h16563, h16570, h16571, h16667, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p16705_1]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h14799, h16563, h16570, h16571, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p16705_1]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h14799, h16563, h16570, h16571, h16576, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p16705_1]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h16564, hlam, p16705_0]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [hlam, p16705_0]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h14799, h16571, h16667, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p16672_1, p16705_1]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h14799, h16571, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p16672_1, p16705_1]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h16576, hlam, p16705_1]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h16567, hlam, p16705_1]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h16573, hlam, p16705_1]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [hlam, p16705_0]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h0, h16567, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p16705_1]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h16668, hlam, p16705_1]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h16569, hlam, p16705_0]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h16575, hlam, p16705_0]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h16667, hlam, p16705_0]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [hlam, p16705_0]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h16670, hlam, p16705_1]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h16570, hlam, p16705_0]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h14799, h16563, h16570, h16571, h16573, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p16705_1]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h14799, h16563, h16570, h16571, h16667, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p16705_1]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [h14799, h16563, h16570, h16571, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p16705_1]
                                                        · have p16705_0 := h16705c.1
                                                          have p16705_1 := h16705c.2.1
                                                          have p16705_2 := h16705c.2.2.1
                                                          have p16705_3 := h16705c.2.2.2
                                                          linarith only [hlam, p16705_0]
                                                · linarith only [h16571, h16698, hlam]
                                              · linarith only [h16565, h16697, hlam]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              rcases p16694_3 (m.d 0 3) (by simp) with h16733 | h16733
                                              · rcases p16694_3 (m.d 1 3) (by simp) with h16734 | h16734
                                                · rcases p16694_3 (m.d 2 3) (by simp) with h16735 | h16735
                                                  · linarith only [h16565, h16735, hlam]
                                                  · linarith only [h16666, h16735, hlam]
                                                · linarith only [h16574, h16734, hlam]
                                              · linarith only [h16733, hlam, p16694_0]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              rcases p16694_3 (m.d 0 3) (by simp) with h16740 | h16740
                                              · rcases p16694_3 (m.d 1 3) (by simp) with h16741 | h16741
                                                · rcases p16694_3 (m.d 2 3) (by simp) with h16742 | h16742
                                                  · linarith only [h16565, h16742, hlam]
                                                  · linarith only [h16667, h16742, hlam]
                                                · linarith only [h16575, h16741, hlam]
                                              · linarith only [h16740, hlam, p16694_0]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [h14799, h16571, h16572, h16576, h16666, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16672_1, p16694_1]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [hlam, p16694_0]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              rcases p16694_3 (m.d 0 3) (by simp) with h16749 | h16749
                                              · linarith only [h14799, h16749, hlam]
                                              · linarith only [h16565, h16749, hlam]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [h14799, h16572, h16576, h16666, hlam, p16672_1, p16694_2]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [h14799, h16575, hlam, p16672_1, p16694_2]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [h16565, hlam, p16694_0]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [h16571, hlam, p16694_0]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [hlam, p16694_0]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              rcases p16694_3 (m.d 0 3) (by simp) with h16757 | h16757
                                              · rcases p16694_3 (m.d 1 3) (by simp) with h16758 | h16758
                                                · rcases p16694_3 (m.d 2 3) (by simp) with h16759 | h16759
                                                  · rcases p16694_3 (m.d 3 4) (by simp) with h16760 | h16760
                                                    · linarith only [h16760, hlam, p16694_0]
                                                    · rcases p16694_3 (m.d 3 5) (by simp) with h16762 | h16762
                                                      · linarith only [h16667, h16762, hlam]
                                                      · linarith only [h16670, h16762, hlam]
                                                  · linarith only [h16759, hlam, p16694_0]
                                                · linarith only [h16574, h16758, hlam]
                                              · linarith only [h16568, h16757, hlam]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              rcases p16694_3 (m.d 0 3) (by simp) with h16768 | h16768
                                              · rcases p16694_3 (m.d 1 3) (by simp) with h16769 | h16769
                                                · rcases p16694_3 (m.d 2 3) (by simp) with h16770 | h16770
                                                  · rcases p16694_3 (m.d 3 4) (by simp) with h16771 | h16771
                                                    · linarith only [h16666, h16771, hlam]
                                                    · rcases p16694_3 (m.d 3 5) (by simp) with h16773 | h16773
                                                      · linarith only [h16773, hlam, p16694_0]
                                                      · rcases h5bigk with h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c | h16775c
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [hlam, p16775_0]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h14799, h16563, h16570, h16572, h16576, h16666, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16775_1]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h14799, h16563, h16570, h16666, h16668, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16775_1]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h14799, h16563, h16570, h16670, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16775_1]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h14799, h16563, h16570, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p16775_1]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h16564, hlam, p16775_0]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [hlam, p16775_0]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h14799, h16571, h16666, h16668, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16672_1, p16775_1]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h14799, h16571, h16670, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16672_1, p16775_1]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h16576, hlam, p16775_1]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h16567, hlam, p16775_1]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h16573, hlam, p16775_1]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [hlam, p16775_0]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h0, h16567, h16670, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16775_1]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h16668, hlam, p16775_1]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h16569, hlam, p16775_0]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h16575, hlam, p16775_0]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h16667, hlam, p16775_0]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [hlam, p16775_0]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h16670, hlam, p16775_1]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h16570, hlam, p16775_0]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h14799, h16563, h16570, h16571, h16573, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p16775_1]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h14799, h16563, h16570, h16571, h16667, h16670, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16775_1]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [h14799, h16563, h16570, h16571, h16670, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16775_1]
                                                        · have p16775_0 := h16775c.1
                                                          have p16775_1 := h16775c.2.1
                                                          have p16775_2 := h16775c.2.2.1
                                                          have p16775_3 := h16775c.2.2.2
                                                          linarith only [hlam, p16775_0]
                                                  · linarith only [h16770, hlam, p16694_0]
                                                · linarith only [h16575, h16769, hlam]
                                              · linarith only [h16569, h16768, hlam]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [h16568, hlam, p16694_0]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [h16574, hlam, p16694_0]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [h16666, hlam, p16694_0]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [hlam, p16694_0]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [h16670, hlam, p16694_1]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [h16569, hlam, p16694_0]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [h16575, hlam, p16694_0]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [h16667, hlam, p16694_0]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [h14799, h16571, h16573, h16667, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16672_1, p16694_1]
                                            · have p16694_0 := h16694c.1
                                              have p16694_1 := h16694c.2.1
                                              have p16694_2 := h16694c.2.2.1
                                              have p16694_3 := h16694c.2.2.2
                                              linarith only [hlam, p16694_0]
                                      · linarith only [h16575, h16689, hlam]
                                    · linarith only [h16573, h16688, hlam]
                                  · linarith only [h16687, hlam, p16672_0]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [h16563, h16570, h16572, h16576, h16666, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16672_1]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [hlam, p16672_0]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [h14799, hc01, hc12, hlam, hphi, p16672_1]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [h0, h16563, h16570, h16576, hlam, p16672_2]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  rcases p16672_3 (m.d 0 1) (by simp) with h16821 | h16821
                                  · linarith only [h0, h16821, hlam]
                                  · linarith only [h16564, h16821, hlam]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [h16563, h16570, h16571, h16576, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p16672_1]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [h16571, hlam, p16672_1]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [hlam, p16672_0]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [h14799, h16563, h16570, h16576, hlam, p16672_2]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  rcases p16672_3 (m.d 0 1) (by simp) with h16828 | h16828
                                  · linarith only [h14799, h16828, hlam]
                                  · linarith only [h16564, h16828, hlam]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [h16563, hlam, p16672_0]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [h16572, hlam, p16672_1]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [h16574, hlam, p16672_0]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [hlam, p16672_0]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [h16576, hlam, p16672_1]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [h16564, hlam, p16672_0]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [h16573, hlam, p16672_1]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [h16575, hlam, p16672_0]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [h14799, h16564, h16572, h16666, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16672_1]
                                · have p16672_0 := h16672c.1
                                  have p16672_1 := h16672c.2.1
                                  have p16672_2 := h16672c.2.2.1
                                  have p16672_3 := h16672c.2.2.2
                                  linarith only [hlam, p16672_0]
                          · linarith only [h14799, h16563, h16570, h16571, h16575, h16576, h16666, h16667, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h14799, h16563, h16570, h16571, h16574, h16576, h16666, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h14799, h16569, h16575, hlam]
                  · linarith only [h0, h14799, h16565, h16568, h16574, hc01, hc12, hlam, hphi]
                · linarith only [h0, h16567, h16573, hlam]
              · linarith only [h0, h16566, h16572, hlam]
            · linarith only [h0, h16565, h16571, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h16848 | h16848
            · rcases m.htr 1 2 4 (by decide) (by decide) with h16849 | h16849
              · rcases m.htr 1 2 5 (by decide) (by decide) with h16850 | h16850
                · rcases m.htr 1 3 4 (by decide) (by decide) with h16851 | h16851
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h16852 | h16852
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h16853 | h16853
                      · linarith only [h14799, h16563, h16570, h16848, h16853, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h16855 | h16855
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h16856 | h16856
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h16857 | h16857
                            · linarith only [h16563, h16570, h16849, h16857, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h16859 | h16859
                              · linarith only [h16563, h16570, h16849, h16855, h16859, hlam]
                              · rcases h1bigk with h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c | h16861c
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  linarith only [hlam, p16861_0]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  linarith only [h0, hlam, p16861_0]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  linarith only [h14799, hlam, p16861_0]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  rcases p16861_3 (m.d 0 1) (by simp) with h16865 | h16865
                                  · rcases p16861_3 (m.d 1 2) (by simp) with h16866 | h16866
                                    · rcases p16861_3 (m.d 1 3) (by simp) with h16867 | h16867
                                      · rcases p16861_3 (m.d 1 4) (by simp) with h16868 | h16868
                                        · linarith only [h16868, hlam, p16861_0]
                                        · rcases p16861_3 (m.d 1 5) (by simp) with h16870 | h16870
                                          · linarith only [h16564, h16870, hlam]
                                          · linarith only [h16853, h16870, hlam]
                                      · linarith only [h16851, h16867, hlam]
                                    · linarith only [h16849, h16866, hlam]
                                  · linarith only [h16865, hlam, p16861_0]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  rcases p16861_3 (m.d 0 1) (by simp) with h16876 | h16876
                                  · rcases p16861_3 (m.d 1 2) (by simp) with h16877 | h16877
                                    · rcases p16861_3 (m.d 1 3) (by simp) with h16878 | h16878
                                      · rcases p16861_3 (m.d 1 4) (by simp) with h16879 | h16879
                                        · linarith only [h16563, h16879, hlam]
                                        · rcases p16861_3 (m.d 1 5) (by simp) with h16881 | h16881
                                          · linarith only [h16881, hlam, p16861_0]
                                          · rcases h3bigk with h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c | h16883c
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [hlam, p16883_0]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [h14799, hlam, p16883_1]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              rcases p16883_3 (m.d 0 3) (by simp) with h16886 | h16886
                                              · rcases p16883_3 (m.d 1 3) (by simp) with h16887 | h16887
                                                · rcases p16883_3 (m.d 2 3) (by simp) with h16888 | h16888
                                                  · linarith only [h16565, h16888, hlam]
                                                  · rcases p16883_3 (m.d 3 4) (by simp) with h16890 | h16890
                                                    · linarith only [h16568, h16890, hlam]
                                                    · rcases p16883_3 (m.d 3 5) (by simp) with h16892 | h16892
                                                      · linarith only [h16569, h16892, hlam]
                                                      · rcases h5bigk with h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c | h16894c
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [hlam, p16894_0]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h14799, h16564, h16848, h16853, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p16894_1]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h14799, h16564, h16848, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p16894_1]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h14799, h16564, h16848, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p16894_1]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h16570, hlam, p16894_1]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h16564, hlam, p16894_0]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [hlam, p16894_0]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h14799, h16848, h16856, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p16861_1, p16894_1]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h14799, h16848, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p16861_1, p16894_1]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h16853, hlam, p16894_1]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h16567, hlam, p16894_1]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h16850, hlam, p16894_1]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [hlam, p16894_0]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h0, h16567, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p16894_1]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h16857, hlam, p16894_1]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h16569, hlam, p16894_0]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h16852, hlam, p16894_0]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h16856, hlam, p16894_0]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [hlam, p16894_0]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h16859, hlam, p16894_1]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h16563, h16570, h16849, h16855, hc34, hc45, hlam, hphi, p16894_1]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h16849, h16853, h16855, hc34, hc45, hlam, hphi, p16894_1]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h16855, h16857, hc34, hc45, hlam, hphi, p16894_1]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [h16859, hc34, hc45, hlam, hphi, p16894_1]
                                                        · have p16894_0 := h16894c.1
                                                          have p16894_1 := h16894c.2.1
                                                          have p16894_2 := h16894c.2.2.1
                                                          have p16894_3 := h16894c.2.2.2
                                                          linarith only [hlam, p16894_0]
                                                · linarith only [h16848, h16887, hlam]
                                              · linarith only [h16565, h16886, hlam]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              rcases p16883_3 (m.d 0 3) (by simp) with h16922 | h16922
                                              · rcases p16883_3 (m.d 1 3) (by simp) with h16923 | h16923
                                                · rcases p16883_3 (m.d 2 3) (by simp) with h16924 | h16924
                                                  · linarith only [h16565, h16924, hlam]
                                                  · linarith only [h16855, h16924, hlam]
                                                · linarith only [h16851, h16923, hlam]
                                              · linarith only [h16922, hlam, p16883_0]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              rcases p16883_3 (m.d 0 3) (by simp) with h16929 | h16929
                                              · rcases p16883_3 (m.d 1 3) (by simp) with h16930 | h16930
                                                · rcases p16883_3 (m.d 2 3) (by simp) with h16931 | h16931
                                                  · linarith only [h16565, h16931, hlam]
                                                  · linarith only [h16856, h16931, hlam]
                                                · linarith only [h16852, h16930, hlam]
                                              · linarith only [h16929, hlam, p16883_0]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [h14799, h16848, h16849, h16853, h16855, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16861_1, p16883_1]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [hlam, p16883_0]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              rcases p16883_3 (m.d 0 3) (by simp) with h16938 | h16938
                                              · linarith only [h14799, h16938, hlam]
                                              · linarith only [h16565, h16938, hlam]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [h14799, h16849, h16853, h16855, hlam, p16861_1, p16883_2]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [h14799, h16852, hlam, p16861_1, p16883_2]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [h16565, hlam, p16883_0]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [h16848, hlam, p16883_0]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [hlam, p16883_0]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              rcases p16883_3 (m.d 0 3) (by simp) with h16946 | h16946
                                              · rcases p16883_3 (m.d 1 3) (by simp) with h16947 | h16947
                                                · rcases p16883_3 (m.d 2 3) (by simp) with h16948 | h16948
                                                  · rcases p16883_3 (m.d 3 4) (by simp) with h16949 | h16949
                                                    · linarith only [h16949, hlam, p16883_0]
                                                    · rcases p16883_3 (m.d 3 5) (by simp) with h16951 | h16951
                                                      · linarith only [h16856, h16951, hlam]
                                                      · linarith only [h16859, h16951, hlam]
                                                  · linarith only [h16948, hlam, p16883_0]
                                                · linarith only [h16851, h16947, hlam]
                                              · linarith only [h16568, h16946, hlam]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              rcases p16883_3 (m.d 0 3) (by simp) with h16957 | h16957
                                              · rcases p16883_3 (m.d 1 3) (by simp) with h16958 | h16958
                                                · rcases p16883_3 (m.d 2 3) (by simp) with h16959 | h16959
                                                  · rcases p16883_3 (m.d 3 4) (by simp) with h16960 | h16960
                                                    · linarith only [h16855, h16960, hlam]
                                                    · rcases p16883_3 (m.d 3 5) (by simp) with h16962 | h16962
                                                      · linarith only [h16962, hlam, p16883_0]
                                                      · rcases h5bigk with h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c | h16964c
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [hlam, p16964_0]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h14799, h16564, h16849, h16853, h16855, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16964_1]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h14799, h16564, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p16964_1]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h14799, h16564, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p16964_1]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h16570, hlam, p16964_1]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h16564, hlam, p16964_0]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [hlam, p16964_0]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h14799, h16848, h16856, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p16861_1, p16964_1]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h14799, h16848, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p16861_1, p16964_1]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h16853, hlam, p16964_1]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h16567, hlam, p16964_1]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h16850, hlam, p16964_1]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [hlam, p16964_0]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h0, h16567, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p16964_1]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h16857, hlam, p16964_1]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h16569, hlam, p16964_0]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h16852, hlam, p16964_0]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h16856, hlam, p16964_0]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [hlam, p16964_0]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h16859, hlam, p16964_1]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h16563, h16570, h16849, h16855, hc34, hc45, hlam, hphi, p16964_1]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h16849, h16853, h16855, hc34, hc45, hlam, hphi, p16964_1]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h16855, h16857, hc34, hc45, hlam, hphi, p16964_1]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [h16859, hc34, hc45, hlam, hphi, p16964_1]
                                                        · have p16964_0 := h16964c.1
                                                          have p16964_1 := h16964c.2.1
                                                          have p16964_2 := h16964c.2.2.1
                                                          have p16964_3 := h16964c.2.2.2
                                                          linarith only [hlam, p16964_0]
                                                  · linarith only [h16959, hlam, p16883_0]
                                                · linarith only [h16852, h16958, hlam]
                                              · linarith only [h16569, h16957, hlam]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [h16568, hlam, p16883_0]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [h16851, hlam, p16883_0]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [h16855, hlam, p16883_0]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [hlam, p16883_0]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [h16859, hlam, p16883_1]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [h16569, hlam, p16883_0]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [h16852, hlam, p16883_0]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [h16856, hlam, p16883_0]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [h14799, h16848, h16852, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16861_1, p16883_1]
                                            · have p16883_0 := h16883c.1
                                              have p16883_1 := h16883c.2.1
                                              have p16883_2 := h16883c.2.2.1
                                              have p16883_3 := h16883c.2.2.2
                                              linarith only [hlam, p16883_0]
                                      · linarith only [h16852, h16878, hlam]
                                    · linarith only [h16850, h16877, hlam]
                                  · linarith only [h16876, hlam, p16861_0]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  rcases p16861_3 (m.d 0 1) (by simp) with h17006 | h17006
                                  · linarith only [h17006, hlam, p16861_0]
                                  · rcases p16861_3 (m.d 1 2) (by simp) with h17008 | h17008
                                    · rcases p16861_3 (m.d 1 3) (by simp) with h17009 | h17009
                                      · linarith only [h16848, h17009, hlam]
                                      · linarith only [h14799, h17009, hlam]
                                    · linarith only [h17008, hlam, p16861_0]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  linarith only [hlam, p16861_0]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  linarith only [h14799, hc01, hc12, hlam, hphi, p16861_1]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  rcases p16861_3 (m.d 0 1) (by simp) with h17015 | h17015
                                  · linarith only [h0, h17015, hlam]
                                  · linarith only [h16563, h17015, hlam]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  rcases p16861_3 (m.d 0 1) (by simp) with h17018 | h17018
                                  · linarith only [h0, h17018, hlam]
                                  · linarith only [h16564, h17018, hlam]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  rcases p16861_3 (m.d 0 1) (by simp) with h17021 | h17021
                                  · linarith only [h17021, hlam, p16861_0]
                                  · rcases p16861_3 (m.d 1 2) (by simp) with h17023 | h17023
                                    · rcases p16861_3 (m.d 1 3) (by simp) with h17024 | h17024
                                      · rcases p16861_3 (m.d 1 4) (by simp) with h17025 | h17025
                                        · linarith only [h16851, h17025, hlam]
                                        · rcases p16861_3 (m.d 1 5) (by simp) with h17027 | h17027
                                          · linarith only [h16852, h17027, hlam]
                                          · rcases h3bigk with h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c | h17029c
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [hlam, p17029_0]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [h14799, hlam, p17029_1]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              rcases p17029_3 (m.d 0 3) (by simp) with h17032 | h17032
                                              · rcases p17029_3 (m.d 1 3) (by simp) with h17033 | h17033
                                                · rcases p17029_3 (m.d 2 3) (by simp) with h17034 | h17034
                                                  · linarith only [h16565, h17034, hlam]
                                                  · rcases p17029_3 (m.d 3 4) (by simp) with h17036 | h17036
                                                    · linarith only [h16568, h17036, hlam]
                                                    · rcases p17029_3 (m.d 3 5) (by simp) with h17038 | h17038
                                                      · linarith only [h16569, h17038, hlam]
                                                      · rcases h5bigk with h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c | h17040c
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [hlam, p17040_0]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16564, h16848, h16850, h16855, h16857, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16861_1, p17040_1]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16564, h16848, h16855, h16857, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16861_1, p17040_1]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16564, h16848, h16859, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16861_1, p17040_1]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16570, hlam, p17040_1]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16564, hlam, p17040_0]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [hlam, p17040_0]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16564, h16848, h16855, h16857, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16861_1, p17040_1]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16564, h16848, h16859, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16861_1, p17040_1]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16853, hlam, p17040_1]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16567, hlam, p17040_1]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16850, hlam, p17040_1]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [hlam, p17040_0]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h0, h16567, h16859, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17040_1]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16857, hlam, p17040_1]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16569, hlam, p17040_0]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16852, hlam, p17040_0]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16856, hlam, p17040_0]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [hlam, p17040_0]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16859, hlam, p17040_1]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16569, h16859, hc34, hc45, hlam, hphi, p17040_1]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16852, h16859, hc34, hc45, hlam, hphi, p17040_1]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16856, h16859, hc34, hc45, hlam, hphi, p17040_1]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [h16859, hc34, hc45, hlam, hphi, p17040_1]
                                                        · have p17040_0 := h17040c.1
                                                          have p17040_1 := h17040c.2.1
                                                          have p17040_2 := h17040c.2.2.1
                                                          have p17040_3 := h17040c.2.2.2
                                                          linarith only [hlam, p17040_0]
                                                · linarith only [h16848, h17033, hlam]
                                              · linarith only [h16565, h17032, hlam]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              rcases p17029_3 (m.d 0 3) (by simp) with h17068 | h17068
                                              · rcases p17029_3 (m.d 1 3) (by simp) with h17069 | h17069
                                                · rcases p17029_3 (m.d 2 3) (by simp) with h17070 | h17070
                                                  · linarith only [h16565, h17070, hlam]
                                                  · linarith only [h16855, h17070, hlam]
                                                · linarith only [h16851, h17069, hlam]
                                              · linarith only [h17068, hlam, p17029_0]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              rcases p17029_3 (m.d 0 3) (by simp) with h17075 | h17075
                                              · rcases p17029_3 (m.d 1 3) (by simp) with h17076 | h17076
                                                · rcases p17029_3 (m.d 2 3) (by simp) with h17077 | h17077
                                                  · linarith only [h16565, h17077, hlam]
                                                  · linarith only [h16856, h17077, hlam]
                                                · linarith only [h16852, h17076, hlam]
                                              · linarith only [h17075, hlam, p17029_0]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              rcases p17029_3 (m.d 0 3) (by simp) with h17082 | h17082
                                              · linarith only [h14799, h17082, hlam]
                                              · rcases p17029_3 (m.d 1 3) (by simp) with h17084 | h17084
                                                · rcases p17029_3 (m.d 2 3) (by simp) with h17085 | h17085
                                                  · linarith only [h16848, h17085, hlam]
                                                  · rcases p17029_3 (m.d 3 4) (by simp) with h17087 | h17087
                                                    · linarith only [h16851, h17087, hlam]
                                                    · rcases p17029_3 (m.d 3 5) (by simp) with h17089 | h17089
                                                      · linarith only [h16852, h17089, hlam]
                                                      · rcases h5bigk with h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c | h17091c
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [hlam, p17091_0]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h14799, h16564, h16848, h16849, h16853, h16855, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17029_1, p17091_1]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h14799, h16564, h16848, h16856, h16859, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17029_1, p17091_1]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h14799, h16564, h16848, h16859, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17029_1, p17091_1]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h16570, hlam, p17091_1]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h16564, hlam, p17091_0]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [hlam, p17091_0]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h14799, h16564, h16848, h16856, h16859, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17029_1, p17091_1]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h14799, h16564, h16848, h16859, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17029_1, p17091_1]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h16853, hlam, p17091_1]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h16567, hlam, p17091_1]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h16850, hlam, p17091_1]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [hlam, p17091_0]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h0, h16567, h16859, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17091_1]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h16857, hlam, p17091_1]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h16569, hlam, p17091_0]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h16852, hlam, p17091_0]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h16856, hlam, p17091_0]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [hlam, p17091_0]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h16859, hlam, p17091_1]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h16569, h16859, hc34, hc45, hlam, hphi, p17091_1]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h16852, h16859, hc34, hc45, hlam, hphi, p17091_1]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h16856, h16859, hc34, hc45, hlam, hphi, p17091_1]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [h16859, hc34, hc45, hlam, hphi, p17091_1]
                                                        · have p17091_0 := h17091c.1
                                                          have p17091_1 := h17091c.2.1
                                                          have p17091_2 := h17091c.2.2.1
                                                          have p17091_3 := h17091c.2.2.2
                                                          linarith only [hlam, p17091_0]
                                                · linarith only [h14799, h17084, hlam]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [hlam, p17029_0]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              rcases p17029_3 (m.d 0 3) (by simp) with h17119 | h17119
                                              · linarith only [h14799, h17119, hlam]
                                              · linarith only [h16565, h17119, hlam]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [h16563, h16849, h16855, hlam, p16861_1, p17029_2]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [h16564, h16850, h16856, hlam, p16861_1, p17029_2]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [h16565, hlam, p17029_0]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [h16848, hlam, p17029_0]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [hlam, p17029_0]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              rcases p17029_3 (m.d 0 3) (by simp) with h17127 | h17127
                                              · rcases p17029_3 (m.d 1 3) (by simp) with h17128 | h17128
                                                · rcases p17029_3 (m.d 2 3) (by simp) with h17129 | h17129
                                                  · rcases p17029_3 (m.d 3 4) (by simp) with h17130 | h17130
                                                    · linarith only [h17130, hlam, p17029_0]
                                                    · rcases p17029_3 (m.d 3 5) (by simp) with h17132 | h17132
                                                      · linarith only [h16856, h17132, hlam]
                                                      · linarith only [h16859, h17132, hlam]
                                                  · linarith only [h17129, hlam, p17029_0]
                                                · linarith only [h16851, h17128, hlam]
                                              · linarith only [h16568, h17127, hlam]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              rcases p17029_3 (m.d 0 3) (by simp) with h17138 | h17138
                                              · rcases p17029_3 (m.d 1 3) (by simp) with h17139 | h17139
                                                · rcases p17029_3 (m.d 2 3) (by simp) with h17140 | h17140
                                                  · rcases p17029_3 (m.d 3 4) (by simp) with h17141 | h17141
                                                    · linarith only [h16855, h17141, hlam]
                                                    · rcases p17029_3 (m.d 3 5) (by simp) with h17143 | h17143
                                                      · linarith only [h17143, hlam, p17029_0]
                                                      · rcases h5bigk with h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c | h17145c
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [hlam, p17145_0]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16564, h16849, h16853, h16855, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16861_1, p17145_1]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16564, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p16861_1, p17145_1]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16564, h16859, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16861_1, p17145_1]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16570, hlam, p17145_1]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16564, hlam, p17145_0]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [hlam, p17145_0]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16564, h16848, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p16861_1, p17145_1]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16564, h16848, h16859, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16861_1, p17145_1]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16853, hlam, p17145_1]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16567, hlam, p17145_1]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16850, hlam, p17145_1]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [hlam, p17145_0]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h0, h16567, h16859, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17145_1]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16857, hlam, p17145_1]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16569, hlam, p17145_0]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16852, hlam, p17145_0]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16856, hlam, p17145_0]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [hlam, p17145_0]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16859, hlam, p17145_1]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16569, h16859, hc34, hc45, hlam, hphi, p17145_1]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16852, h16859, hc34, hc45, hlam, hphi, p17145_1]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16856, h16859, hc34, hc45, hlam, hphi, p17145_1]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [h16859, hc34, hc45, hlam, hphi, p17145_1]
                                                        · have p17145_0 := h17145c.1
                                                          have p17145_1 := h17145c.2.1
                                                          have p17145_2 := h17145c.2.2.1
                                                          have p17145_3 := h17145c.2.2.2
                                                          linarith only [hlam, p17145_0]
                                                  · linarith only [h17140, hlam, p17029_0]
                                                · linarith only [h16852, h17139, hlam]
                                              · linarith only [h16569, h17138, hlam]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [h16568, hlam, p17029_0]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [h16851, hlam, p17029_0]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [h16855, hlam, p17029_0]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [hlam, p17029_0]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [h16859, hlam, p17029_1]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [h16569, hlam, p17029_0]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [h16852, hlam, p17029_0]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [h16856, hlam, p17029_0]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [h16564, h16567, h16848, h16856, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16861_1, p17029_1]
                                            · have p17029_0 := h17029c.1
                                              have p17029_1 := h17029c.2.1
                                              have p17029_2 := h17029c.2.2.1
                                              have p17029_3 := h17029c.2.2.2
                                              linarith only [hlam, p17029_0]
                                      · linarith only [h17024, hlam, p16861_0]
                                    · linarith only [h0, h17023, hlam]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  linarith only [h16848, hlam, p16861_1]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  linarith only [hlam, p16861_0]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  rcases p16861_3 (m.d 0 1) (by simp) with h17188 | h17188
                                  · linarith only [h14799, h17188, hlam]
                                  · linarith only [h16563, h17188, hlam]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  rcases p16861_3 (m.d 0 1) (by simp) with h17191 | h17191
                                  · linarith only [h14799, h17191, hlam]
                                  · linarith only [h16564, h17191, hlam]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  linarith only [h16563, hlam, p16861_0]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  linarith only [h16849, hlam, p16861_1]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  linarith only [h16851, hlam, p16861_0]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  linarith only [hlam, p16861_0]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  linarith only [h16853, hlam, p16861_1]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  linarith only [h16564, hlam, p16861_0]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  linarith only [h16850, hlam, p16861_1]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  linarith only [h16852, hlam, p16861_0]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  linarith only [h14799, h16564, h16848, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p16861_1]
                                · have p16861_0 := h16861c.1
                                  have p16861_1 := h16861c.2.1
                                  have p16861_2 := h16861c.2.2.1
                                  have p16861_3 := h16861c.2.2.2
                                  linarith only [hlam, p16861_0]
                          · linarith only [h14799, h16564, h16848, h16852, h16855, h16856, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h17205 | h17205
                          · linarith only [h14799, h16563, h16848, h16851, h16855, h17205, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h17207 | h17207
                            · linarith only [h16563, h16570, h16851, h16855, h17207, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h17209 | h17209
                              · linarith only [h16563, h16570, h16851, h17209, hlam]
                              · rcases h1bigk with h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c | h17211c
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [hlam, p17211_0]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [h0, hlam, p17211_0]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [h14799, hlam, p17211_0]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [h14799, h16848, h16851, h16855, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17211_1]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [h14799, h16848, h16851, h16853, h16855, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17211_1]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [h16563, h16851, h16855, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17211_1]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [hlam, p17211_0]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [h14799, hc01, hc12, hlam, hphi, p17211_1]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  rcases p17211_3 (m.d 0 1) (by simp) with h17220 | h17220
                                  · linarith only [h0, h17220, hlam]
                                  · linarith only [h16563, h17220, hlam]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  rcases p17211_3 (m.d 0 1) (by simp) with h17223 | h17223
                                  · linarith only [h0, h17223, hlam]
                                  · linarith only [h16564, h17223, hlam]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [h16564, h16851, h16853, h16855, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17211_1]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [h16848, hlam, p17211_1]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [hlam, p17211_0]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  rcases p17211_3 (m.d 0 1) (by simp) with h17229 | h17229
                                  · linarith only [h14799, h17229, hlam]
                                  · linarith only [h16563, h17229, hlam]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  rcases p17211_3 (m.d 0 1) (by simp) with h17232 | h17232
                                  · linarith only [h14799, h17232, hlam]
                                  · linarith only [h16564, h17232, hlam]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [h16563, hlam, p17211_0]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [h16849, hlam, p17211_1]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [h16851, hlam, p17211_0]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [hlam, p17211_0]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [h16853, hlam, p17211_1]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [h16564, hlam, p17211_0]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [h16850, hlam, p17211_1]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [h16852, hlam, p17211_0]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [h16564, h16851, h16855, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17211_1]
                                · have p17211_0 := h17211c.1
                                  have p17211_1 := h17211c.2.1
                                  have p17211_2 := h17211c.2.2.1
                                  have p17211_3 := h17211c.2.2.2
                                  linarith only [hlam, p17211_0]
                    · linarith only [h0, h14799, h16565, h16569, h16852, hc01, hc12, hlam, hphi]
                  · linarith only [h14799, h16568, h16851, hlam]
                · linarith only [h0, h16567, h16850, hlam]
              · linarith only [h0, h16566, h16849, hlam]
            · linarith only [h0, h16565, h16848, hlam]
        · linarith only [h14799, h16564, h16569, hlam]
      · linarith only [h14799, h16563, h16568, hlam]
    · linarith only [h14799, h16564, h16565, h16567, hlam]
  · linarith only [h14799, h16563, h16565, h16566, hlam]

end R2N4
