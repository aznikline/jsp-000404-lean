import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h15534 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h15535 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h15536 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h15537 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h15538 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h15539 | h15539
  · rcases m.htr 0 4 5 (by decide) (by decide) with h15540 | h15540
    · rcases m.htr 1 2 3 (by decide) (by decide) with h15541 | h15541
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15542 | h15542
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15543 | h15543
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15544 | h15544
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15545 | h15545
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15546 | h15546
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15547 | h15547
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15548 | h15548
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15549 | h15549
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15550 | h15550
                        · linarith only [h0, h15532, h15541, h15547, h15550, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h15532, h15544, h15546, h15550, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h15532, h15544, h15546, h15549, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h15532, h15545, h15548, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h15532, h15544, h15547, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15556 | h15556
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15557 | h15557
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15558 | h15558
                      · linarith only [h15542, h15546, h15558, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15560 | h15560
                        · linarith only [h15535, h15546, h15556, h15560, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h0bigk with h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c | h15562c
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [hlam, p15562_0]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h0, hlam, p15562_1]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h0, h15532, h15541, h15557, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p15562_1]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h0, h15540, h15542, h15546, h15556, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15562_1]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h0, h15540, h15542, h15546, h15556, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15562_1]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h0, h15532, h15541, h15557, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p15562_1]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [hlam, p15562_0]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h0, h15538, h15540, h15542, h15546, h15556, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15562_1]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h0, h15540, h15542, h15546, h15556, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15562_1]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            rcases p15562_3 (m.d 0 1) (by simp) with h15572 | h15572
                            · linarith only [h0, h15572, hlam]
                            · linarith only [h15534, h15572, hlam]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h15532, hlam, p15562_1]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h15535, hlam, p15562_1]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [hlam, p15562_0]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h15532, h15540, h15542, h15546, h15556, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15562_1]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h0, h15532, h15540, h15542, h15546, h15556, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15562_1]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h15533, hlam, p15562_0]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h15536, hlam, p15562_0]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h15538, hlam, p15562_0]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [hlam, p15562_0]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h0, h15533, h15540, h15542, h15546, h15556, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15562_1]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h15534, hlam, p15562_0]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h15537, hlam, p15562_1]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h15539, hlam, p15562_0]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [h15540, hlam, p15562_1]
                          · have p15562_0 := h15562c.1
                            have p15562_1 := h15562c.2.1
                            have p15562_2 := h15562c.2.2.1
                            have p15562_3 := h15562c.2.2.2
                            linarith only [hlam, p15562_0]
                    · linarith only [h0, h15532, h15545, h15557, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h15532, h15544, h15556, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h15532, h15539, h15544, h15545, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15593 | h15593
              · linarith only [h0, h15532, h15538, h15544, h15593, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15595 | h15595
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15596 | h15596
                  · linarith only [h15541, h15544, h15596, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15598 | h15598
                    · linarith only [h15541, h15593, h15598, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15600 | h15600
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15601 | h15601
                        · rcases h0bigk with h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c | h15602c
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [hlam, p15602_0]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h0, hlam, p15602_1]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h0, h15538, h15593, h15601, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15602_1]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h0, h15533, h15542, h15600, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15602_1]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h0, h15539, h15593, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15602_1]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h0, h15532, h15538, h15593, h15601, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15602_1]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [hlam, p15602_0]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h0, h15538, h15593, h15601, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15602_1]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            rcases p15602_3 (m.d 0 1) (by simp) with h15611 | h15611
                            · linarith only [h0, h15611, hlam]
                            · linarith only [h15533, h15611, hlam]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            rcases p15602_3 (m.d 0 1) (by simp) with h15614 | h15614
                            · linarith only [h0, h15614, hlam]
                            · linarith only [h15534, h15614, hlam]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h15532, hlam, p15602_1]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h15535, hlam, p15602_1]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [hlam, p15602_0]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h0, h15532, h15538, h15541, h15593, h15601, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15602_1]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h0, h15532, h15539, h15541, h15593, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15602_1]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h15533, hlam, p15602_0]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h15536, hlam, p15602_0]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h15538, hlam, p15602_0]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [hlam, p15602_0]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h0, h15533, h15539, h15541, h15593, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15602_1]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h15534, hlam, p15602_0]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h15537, hlam, p15602_1]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h15539, hlam, p15602_0]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [h15540, hlam, p15602_1]
                          · have p15602_0 := h15602c.1
                            have p15602_1 := h15602c.2.1
                            have p15602_2 := h15602c.2.2.1
                            have p15602_3 := h15602c.2.2.2
                            linarith only [hlam, p15602_0]
                        · linarith only [h0, h15533, h15542, h15600, h15601, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h15532, h15538, h15544, h15595, h15600, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15634 | h15634
                  · linarith only [h0, h15532, h15539, h15541, h15593, h15634, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15636 | h15636
                    · linarith only [h0, h15532, h15538, h15540, h15541, h15544, h15595, h15636, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15638 | h15638
                      · linarith only [h15542, h15595, h15638, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15640 | h15640
                        · linarith only [h0, h15532, h15538, h15595, h15640, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h15532, h15538, h15540, h15541, h15544, h15640, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · linarith only [h0, h15537, h15543, hlam]
        · linarith only [h0, h15536, h15542, hlam]
      · linarith only [h0, h15535, h15541, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h15646 | h15646
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15647 | h15647
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15648 | h15648
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15649 | h15649
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15650 | h15650
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15651 | h15651
                · linarith only [h0, h15533, h15540, h15651, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15653 | h15653
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15654 | h15654
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15655 | h15655
                      · linarith only [h15534, h15540, h15647, h15651, h15655, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15657 | h15657
                        · linarith only [h15532, h15533, h15540, h15646, h15647, h15653, h15657, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h0bigk with h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c | h15659c
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            linarith only [hlam, p15659_0]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            linarith only [h0, hlam, p15659_1]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            linarith only [h0, h15538, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15659_1]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            rcases p15659_3 (m.d 0 1) (by simp) with h15663 | h15663
                            · rcases p15659_3 (m.d 0 2) (by simp) with h15664 | h15664
                              · rcases p15659_3 (m.d 0 3) (by simp) with h15665 | h15665
                                · linarith only [h15532, h15665, hlam]
                                · linarith only [h15538, h15665, hlam]
                              · linarith only [h15536, h15664, hlam]
                            · linarith only [h15533, h15663, hlam]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            rcases p15659_3 (m.d 0 1) (by simp) with h15670 | h15670
                            · rcases p15659_3 (m.d 0 2) (by simp) with h15671 | h15671
                              · rcases p15659_3 (m.d 0 3) (by simp) with h15672 | h15672
                                · linarith only [h15532, h15672, hlam]
                                · linarith only [h15539, h15672, hlam]
                              · linarith only [h15537, h15671, hlam]
                            · linarith only [h15534, h15670, hlam]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            linarith only [h0, h15532, h15646, h15654, h15657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15659_1]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            linarith only [hlam, p15659_0]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            rcases p15659_3 (m.d 0 1) (by simp) with h15679 | h15679
                            · linarith only [h0, h15679, hlam]
                            · linarith only [h15532, h15679, hlam]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            rcases p15659_3 (m.d 0 1) (by simp) with h15682 | h15682
                            · linarith only [h0, h15682, hlam]
                            · linarith only [h15533, h15682, hlam]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            rcases p15659_3 (m.d 0 1) (by simp) with h15685 | h15685
                            · linarith only [h0, h15685, hlam]
                            · linarith only [h15534, h15685, hlam]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            linarith only [h15532, hlam, p15659_1]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            linarith only [h15535, hlam, p15659_1]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            linarith only [hlam, p15659_0]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            rcases p15659_3 (m.d 0 1) (by simp) with h15691 | h15691
                            · rcases p15659_3 (m.d 0 2) (by simp) with h15692 | h15692
                              · rcases p15659_3 (m.d 0 3) (by simp) with h15693 | h15693
                                · rcases p15659_3 (m.d 0 4) (by simp) with h15694 | h15694
                                  · linarith only [h15538, h15694, hlam]
                                  · rcases p15659_3 (m.d 0 5) (by simp) with h15696 | h15696
                                    · linarith only [h15539, h15696, hlam]
                                    · linarith only [h15540, h15696, hlam]
                                · linarith only [h15538, h15693, hlam]
                              · linarith only [h15536, h15692, hlam]
                            · linarith only [h15533, h15691, hlam]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            rcases p15659_3 (m.d 0 1) (by simp) with h15702 | h15702
                            · rcases p15659_3 (m.d 0 2) (by simp) with h15703 | h15703
                              · rcases p15659_3 (m.d 0 3) (by simp) with h15704 | h15704
                                · rcases p15659_3 (m.d 0 4) (by simp) with h15705 | h15705
                                  · linarith only [h15538, h15705, hlam]
                                  · rcases p15659_3 (m.d 0 5) (by simp) with h15707 | h15707
                                    · linarith only [h15539, h15707, hlam]
                                    · rcases h2bigk with h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c | h15709c
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [hlam, p15709_0]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [h0, hlam, p15709_1]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        rcases p15709_3 (m.d 0 2) (by simp) with h15712 | h15712
                                        · rcases p15709_3 (m.d 1 2) (by simp) with h15713 | h15713
                                          · rcases p15709_3 (m.d 2 3) (by simp) with h15714 | h15714
                                            · linarith only [h15714, hlam, p15709_0]
                                            · rcases p15709_3 (m.d 2 4) (by simp) with h15716 | h15716
                                              · linarith only [h15536, h15716, hlam]
                                              · rcases p15709_3 (m.d 2 5) (by simp) with h15718 | h15718
                                                · linarith only [h15537, h15718, hlam]
                                                · rcases h3bigk with h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c | h15720c
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [hlam, p15720_0]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [h0, h15532, h15646, h15654, h15657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15720_1]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [h0, h15532, h15654, h15657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15720_1]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    rcases p15720_3 (m.d 0 3) (by simp) with h15724 | h15724
                                                    · rcases p15720_3 (m.d 1 3) (by simp) with h15725 | h15725
                                                      · linarith only [h15532, h15725, hlam]
                                                      · linarith only [h15649, h15725, hlam]
                                                    · linarith only [h15724, hlam, p15720_0]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    rcases p15720_3 (m.d 0 3) (by simp) with h15729 | h15729
                                                    · rcases p15720_3 (m.d 1 3) (by simp) with h15730 | h15730
                                                      · linarith only [h15532, h15730, hlam]
                                                      · linarith only [h15650, h15730, hlam]
                                                    · linarith only [h15729, hlam, p15720_0]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [h15532, hlam, p15720_0]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [hlam, p15720_0]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [h0, h15532, h15654, h15657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15720_1]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [h0, h15532, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15720_1]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [h0, h15532, h15657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15720_1]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [h15535, hlam, p15720_0]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [h15646, hlam, p15720_0]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [hlam, p15720_0]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p15709_1, p15720_1]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [h0, h15657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15709_1, p15720_1]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [h15538, hlam, p15720_0]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [h15649, hlam, p15720_0]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [h15653, hlam, p15720_0]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [hlam, p15720_0]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [h15657, hlam, p15720_1]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [h15539, hlam, p15720_0]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [h15650, hlam, p15720_0]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [h15654, hlam, p15720_0]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [h0, h15532, h15539, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15720_1]
                                                  · have p15720_0 := h15720c.1
                                                    have p15720_1 := h15720c.2.1
                                                    have p15720_2 := h15720c.2.2.1
                                                    have p15720_3 := h15720c.2.2.2
                                                    linarith only [hlam, p15720_0]
                                          · linarith only [h15646, h15713, hlam]
                                        · linarith only [h15712, hlam, p15709_0]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        rcases p15709_3 (m.d 0 2) (by simp) with h15756 | h15756
                                        · rcases p15709_3 (m.d 1 2) (by simp) with h15757 | h15757
                                          · rcases p15709_3 (m.d 2 3) (by simp) with h15758 | h15758
                                            · linarith only [h15535, h15758, hlam]
                                            · linarith only [h15653, h15758, hlam]
                                          · linarith only [h15647, h15757, hlam]
                                        · linarith only [h15756, hlam, p15709_0]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        rcases p15709_3 (m.d 0 2) (by simp) with h15763 | h15763
                                        · rcases p15709_3 (m.d 1 2) (by simp) with h15764 | h15764
                                          · rcases p15709_3 (m.d 2 3) (by simp) with h15765 | h15765
                                            · linarith only [h15535, h15765, hlam]
                                            · linarith only [h15654, h15765, hlam]
                                          · linarith only [h15648, h15764, hlam]
                                        · linarith only [h15763, hlam, p15709_0]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [h15535, h15654, h15657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15709_1]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [hlam, p15709_0]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        rcases p15709_3 (m.d 0 2) (by simp) with h15772 | h15772
                                        · linarith only [h0, h15772, hlam]
                                        · linarith only [h15535, h15772, hlam]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [h0, h15532, h15534, h15647, h15651, hlam, p15659_1, p15709_2]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [h0, h15532, h15534, h15648, hlam, p15659_1, p15709_2]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [h15535, hlam, p15709_0]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [h15646, hlam, p15709_0]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [hlam, p15709_0]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [h0, h15532, h15646, h15653, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15709_1]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [h0, h15532, h15646, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p15709_1]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [h15536, hlam, p15709_0]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [h15647, hlam, p15709_0]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [h15653, hlam, p15709_1]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [hlam, p15709_0]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [h15655, hlam, p15709_1]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [h15537, hlam, p15709_0]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [h15648, hlam, p15709_0]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [h15654, hlam, p15709_1]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [h15537, h15653, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p15659_1, p15709_1]
                                      · have p15709_0 := h15709c.1
                                        have p15709_1 := h15709c.2.1
                                        have p15709_2 := h15709c.2.2.1
                                        have p15709_3 := h15709c.2.2.2
                                        linarith only [hlam, p15709_0]
                                · linarith only [h15539, h15704, hlam]
                              · linarith only [h15537, h15703, hlam]
                            · linarith only [h15534, h15702, hlam]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            linarith only [h15533, hlam, p15659_0]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            linarith only [h15536, hlam, p15659_0]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            linarith only [h15538, hlam, p15659_0]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            linarith only [hlam, p15659_0]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            linarith only [h15540, hlam, p15659_0]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            linarith only [h15534, hlam, p15659_0]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            linarith only [h15537, hlam, p15659_1]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            linarith only [h15539, hlam, p15659_0]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            rcases p15659_3 (m.d 0 1) (by simp) with h15803 | h15803
                            · rcases p15659_3 (m.d 0 2) (by simp) with h15804 | h15804
                              · rcases p15659_3 (m.d 0 3) (by simp) with h15805 | h15805
                                · rcases p15659_3 (m.d 0 4) (by simp) with h15806 | h15806
                                  · linarith only [h15540, h15806, hlam]
                                  · rcases p15659_3 (m.d 0 5) (by simp) with h15808 | h15808
                                    · rcases h2bigk with h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c | h15809c
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [hlam, p15809_0]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [h0, hlam, p15809_1]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        rcases p15809_3 (m.d 0 2) (by simp) with h15812 | h15812
                                        · rcases p15809_3 (m.d 1 2) (by simp) with h15813 | h15813
                                          · rcases p15809_3 (m.d 2 3) (by simp) with h15814 | h15814
                                            · linarith only [h15814, hlam, p15809_0]
                                            · rcases p15809_3 (m.d 2 4) (by simp) with h15816 | h15816
                                              · linarith only [h15536, h15816, hlam]
                                              · rcases p15809_3 (m.d 2 5) (by simp) with h15818 | h15818
                                                · linarith only [h15537, h15818, hlam]
                                                · rcases h3bigk with h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c | h15820c
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [hlam, p15820_0]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [h0, h15532, h15646, h15654, h15657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15820_1]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [h0, h15532, h15654, h15657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15820_1]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    rcases p15820_3 (m.d 0 3) (by simp) with h15824 | h15824
                                                    · rcases p15820_3 (m.d 1 3) (by simp) with h15825 | h15825
                                                      · linarith only [h15532, h15825, hlam]
                                                      · linarith only [h15649, h15825, hlam]
                                                    · linarith only [h15824, hlam, p15820_0]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    rcases p15820_3 (m.d 0 3) (by simp) with h15829 | h15829
                                                    · rcases p15820_3 (m.d 1 3) (by simp) with h15830 | h15830
                                                      · linarith only [h15532, h15830, hlam]
                                                      · linarith only [h15650, h15830, hlam]
                                                    · linarith only [h15829, hlam, p15820_0]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [h15532, hlam, p15820_0]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [hlam, p15820_0]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [h0, h15532, h15654, h15657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15820_1]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [h0, h15532, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15820_1]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [h0, h15532, h15657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15820_1]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [h15535, hlam, p15820_0]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [h15646, hlam, p15820_0]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [hlam, p15820_0]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p15809_1, p15820_1]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [h0, h15657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15809_1, p15820_1]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [h15538, hlam, p15820_0]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [h15649, hlam, p15820_0]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [h15653, hlam, p15820_0]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [hlam, p15820_0]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [h15657, hlam, p15820_1]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [h15539, hlam, p15820_0]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [h15650, hlam, p15820_0]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [h15654, hlam, p15820_0]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [h0, h15532, h15539, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15820_1]
                                                  · have p15820_0 := h15820c.1
                                                    have p15820_1 := h15820c.2.1
                                                    have p15820_2 := h15820c.2.2.1
                                                    have p15820_3 := h15820c.2.2.2
                                                    linarith only [hlam, p15820_0]
                                          · linarith only [h15646, h15813, hlam]
                                        · linarith only [h15812, hlam, p15809_0]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        rcases p15809_3 (m.d 0 2) (by simp) with h15856 | h15856
                                        · rcases p15809_3 (m.d 1 2) (by simp) with h15857 | h15857
                                          · rcases p15809_3 (m.d 2 3) (by simp) with h15858 | h15858
                                            · linarith only [h15535, h15858, hlam]
                                            · linarith only [h15653, h15858, hlam]
                                          · linarith only [h15647, h15857, hlam]
                                        · linarith only [h15856, hlam, p15809_0]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        rcases p15809_3 (m.d 0 2) (by simp) with h15863 | h15863
                                        · rcases p15809_3 (m.d 1 2) (by simp) with h15864 | h15864
                                          · rcases p15809_3 (m.d 2 3) (by simp) with h15865 | h15865
                                            · linarith only [h15535, h15865, hlam]
                                            · linarith only [h15654, h15865, hlam]
                                          · linarith only [h15648, h15864, hlam]
                                        · linarith only [h15863, hlam, p15809_0]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [h0, h15533, h15534, h15647, h15653, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15659_1, p15809_1]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [hlam, p15809_0]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        rcases p15809_3 (m.d 0 2) (by simp) with h15872 | h15872
                                        · linarith only [h0, h15872, hlam]
                                        · linarith only [h15535, h15872, hlam]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [h0, h15532, h15533, h15539, h15647, hlam, p15659_1, p15809_2]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        rcases p15809_3 (m.d 0 2) (by simp) with h15876 | h15876
                                        · linarith only [h0, h15876, hlam]
                                        · linarith only [h15537, h15876, hlam]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [h15535, hlam, p15809_0]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [h15646, hlam, p15809_0]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [hlam, p15809_0]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [h0, h15532, h15646, h15653, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15809_1]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [h0, h15532, h15646, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p15809_1]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [h15536, hlam, p15809_0]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [h15647, hlam, p15809_0]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [h15653, hlam, p15809_1]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [hlam, p15809_0]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [h15655, hlam, p15809_1]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [h15537, hlam, p15809_0]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [h15648, hlam, p15809_0]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [h15654, hlam, p15809_1]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [h0, h15532, h15648, h15650, h15653, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15809_1]
                                      · have p15809_0 := h15809c.1
                                        have p15809_1 := h15809c.2.1
                                        have p15809_2 := h15809c.2.2.1
                                        have p15809_3 := h15809c.2.2.2
                                        linarith only [hlam, p15809_0]
                                    · linarith only [h15540, h15808, hlam]
                                · linarith only [h15538, h15805, hlam]
                              · linarith only [h15536, h15804, hlam]
                            · linarith only [h15533, h15803, hlam]
                          · have p15659_0 := h15659c.1
                            have p15659_1 := h15659c.2.1
                            have p15659_2 := h15659c.2.2.1
                            have p15659_3 := h15659c.2.2.2
                            linarith only [hlam, p15659_0]
                    · linarith only [h0, h15532, h15650, h15654, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h15532, h15649, h15653, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h15532, h15539, h15649, h15650, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15902 | h15902
              · linarith only [h0, h15532, h15538, h15649, h15902, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15904 | h15904
                · linarith only [h0, h15533, h15540, h15904, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15906 | h15906
                  · linarith only [h15646, h15649, h15906, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15908 | h15908
                    · linarith only [h0, h15532, h15538, h15646, h15648, h15649, h15902, h15908, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15910 | h15910
                      · linarith only [h15533, h15538, h15540, h15646, h15647, h15649, h15910, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15912 | h15912
                        · linarith only [h15538, h15540, h15912, hlam]
                        · rcases h0bigk with h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c | h15914c
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [hlam, p15914_0]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h0, hlam, p15914_1]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h0, h15539, h15902, h15904, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p15914_1]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h0, h15538, h15646, h15649, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15914_1]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h0, h15538, h15540, h15646, h15649, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15914_1]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h0, h15532, h15538, h15646, h15649, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15914_1]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [hlam, p15914_0]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h0, h15538, h15646, h15649, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15914_1]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            rcases p15914_3 (m.d 0 1) (by simp) with h15923 | h15923
                            · linarith only [h0, h15923, hlam]
                            · linarith only [h15533, h15923, hlam]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            rcases p15914_3 (m.d 0 1) (by simp) with h15926 | h15926
                            · linarith only [h0, h15926, hlam]
                            · linarith only [h15534, h15926, hlam]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h15532, hlam, p15914_1]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h15535, hlam, p15914_1]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [hlam, p15914_0]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h0, h15532, h15538, h15646, h15649, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15914_1]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h0, h15532, h15538, h15540, h15646, h15649, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15914_1]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h15533, hlam, p15914_0]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h15536, hlam, p15914_0]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h15538, hlam, p15914_0]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [hlam, p15914_0]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h15540, hlam, p15914_0]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h15534, hlam, p15914_0]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h15537, hlam, p15914_1]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h15539, hlam, p15914_0]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [h0, h15534, h15538, h15646, h15649, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15914_1]
                          · have p15914_0 := h15914c.1
                            have p15914_1 := h15914c.2.1
                            have p15914_2 := h15914c.2.2.1
                            have p15914_3 := h15914c.2.2.2
                            linarith only [hlam, p15914_0]
          · linarith only [h0, h15537, h15648, hlam]
        · linarith only [h0, h15536, h15647, hlam]
      · linarith only [h0, h15535, h15646, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h15947 | h15947
    · linarith only [h15538, h15539, h15947, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h15949 | h15949
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15950 | h15950
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15951 | h15951
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15952 | h15952
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15953 | h15953
              · linarith only [h0, h15532, h15539, h15953, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15955 | h15955
                · linarith only [h0, h15533, h15947, h15955, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15957 | h15957
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15958 | h15958
                    · linarith only [h15532, h15539, h15949, h15958, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15960 | h15960
                      · linarith only [h15533, h15538, h15539, h15947, h15950, h15960, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15962 | h15962
                        · linarith only [h15535, h15947, h15957, h15962, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h0bigk with h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c | h15964c
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [hlam, p15964_0]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [h0, hlam, p15964_1]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [h0, h15532, h15949, h15957, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15964_1]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            rcases p15964_3 (m.d 0 1) (by simp) with h15968 | h15968
                            · rcases p15964_3 (m.d 0 2) (by simp) with h15969 | h15969
                              · rcases p15964_3 (m.d 0 3) (by simp) with h15970 | h15970
                                · linarith only [h15532, h15970, hlam]
                                · linarith only [h15538, h15970, hlam]
                              · linarith only [h15536, h15969, hlam]
                            · linarith only [h15533, h15968, hlam]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [h0, h15532, h15539, h15949, h15957, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15964_1]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [h0, h15532, h15949, h15957, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15964_1]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [hlam, p15964_0]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            rcases p15964_3 (m.d 0 1) (by simp) with h15978 | h15978
                            · linarith only [h0, h15978, hlam]
                            · linarith only [h15532, h15978, hlam]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            rcases p15964_3 (m.d 0 1) (by simp) with h15981 | h15981
                            · linarith only [h0, h15981, hlam]
                            · linarith only [h15533, h15981, hlam]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            rcases p15964_3 (m.d 0 1) (by simp) with h15984 | h15984
                            · linarith only [h0, h15984, hlam]
                            · linarith only [h15534, h15984, hlam]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [h15532, hlam, p15964_1]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [h15535, hlam, p15964_1]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [hlam, p15964_0]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [h15539, h15962, hc04, hc45, hlam, hphi, p15964_1]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [h15539, hlam, p15964_1]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [h15533, hlam, p15964_0]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [h15536, hlam, p15964_0]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [h15538, hlam, p15964_0]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [hlam, p15964_0]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [h15947, hlam, p15964_0]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [h15534, hlam, p15964_0]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [h15537, hlam, p15964_1]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [h0, h15532, h15534, h15949, h15957, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15964_1]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            rcases p15964_3 (m.d 0 1) (by simp) with h16000 | h16000
                            · rcases p15964_3 (m.d 0 2) (by simp) with h16001 | h16001
                              · rcases p15964_3 (m.d 0 3) (by simp) with h16002 | h16002
                                · linarith only [h15539, h16002, hlam]
                                · linarith only [h15538, h16002, hlam]
                              · linarith only [h15536, h16001, hlam]
                            · linarith only [h15533, h16000, hlam]
                          · have p15964_0 := h15964c.1
                            have p15964_1 := h15964c.2.1
                            have p15964_2 := h15964c.2.2.1
                            have p15964_3 := h15964c.2.2.2
                            linarith only [hlam, p15964_0]
                  · linarith only [h15538, h15539, h15957, hc23, hc35, hlam, hphi]
            · linarith only [h15538, h15539, h15949, h15952, hc23, hc35, hlam, hphi]
          · linarith only [h0, h15537, h15951, hlam]
        · linarith only [h0, h15536, h15950, hlam]
      · linarith only [h0, h15535, h15949, hlam]

set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h15534 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h15535 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h15536 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h15537 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h15538 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h16013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h16014 | h16014
  · rcases m.htr 1 2 3 (by decide) (by decide) with h16015 | h16015
    · rcases m.htr 1 2 4 (by decide) (by decide) with h16016 | h16016
      · rcases m.htr 1 2 5 (by decide) (by decide) with h16017 | h16017
        · rcases m.htr 1 3 4 (by decide) (by decide) with h16018 | h16018
          · linarith only [h15532, h15538, h16018, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h16020 | h16020
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16021 | h16021
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16022 | h16022
                · linarith only [h15532, h15538, h16015, h16022, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16024 | h16024
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16025 | h16025
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16026 | h16026
                      · rcases h0bigk with h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c | h16027c
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [hlam, p16027_0]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [h0, hlam, p16027_1]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [h0, h15532, h16015, h16024, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p16027_1]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [h0, h15532, h15538, h16015, h16024, h16026, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16027_1]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          rcases p16027_3 (m.d 0 1) (by simp) with h16032 | h16032
                          · rcases p16027_3 (m.d 0 2) (by simp) with h16033 | h16033
                            · rcases p16027_3 (m.d 0 3) (by simp) with h16034 | h16034
                              · linarith only [h15532, h16034, hlam]
                              · linarith only [h16013, h16034, hlam]
                            · linarith only [h15537, h16033, hlam]
                          · linarith only [h15534, h16032, hlam]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [h0, h15532, h16015, h16024, h16026, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16027_1]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [hlam, p16027_0]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          rcases p16027_3 (m.d 0 1) (by simp) with h16041 | h16041
                          · linarith only [h0, h16041, hlam]
                          · linarith only [h15532, h16041, hlam]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          rcases p16027_3 (m.d 0 1) (by simp) with h16044 | h16044
                          · linarith only [h0, h16044, hlam]
                          · linarith only [h15533, h16044, hlam]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          rcases p16027_3 (m.d 0 1) (by simp) with h16047 | h16047
                          · linarith only [h0, h16047, hlam]
                          · linarith only [h15534, h16047, hlam]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [h15532, hlam, p16027_1]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [h15535, hlam, p16027_1]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [hlam, p16027_0]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [h15538, hlam, p16027_1]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          rcases p16027_3 (m.d 0 1) (by simp) with h16054 | h16054
                          · rcases p16027_3 (m.d 0 2) (by simp) with h16055 | h16055
                            · rcases p16027_3 (m.d 0 3) (by simp) with h16056 | h16056
                              · rcases p16027_3 (m.d 0 4) (by simp) with h16057 | h16057
                                · rcases p16027_3 (m.d 0 5) (by simp) with h16058 | h16058
                                  · linarith only [h16013, h16058, hlam]
                                  · rcases h2bigk with h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c | h16060c
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [hlam, p16060_0]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [h0, hlam, p16060_1]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      rcases p16060_3 (m.d 0 2) (by simp) with h16063 | h16063
                                      · rcases p16060_3 (m.d 1 2) (by simp) with h16064 | h16064
                                        · rcases p16060_3 (m.d 2 3) (by simp) with h16065 | h16065
                                          · linarith only [h16065, hlam, p16060_0]
                                          · rcases p16060_3 (m.d 2 4) (by simp) with h16067 | h16067
                                            · linarith only [h15536, h16067, hlam]
                                            · linarith only [h16022, h16067, hlam]
                                        · linarith only [h16015, h16064, hlam]
                                      · linarith only [h16063, hlam, p16060_0]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      rcases p16060_3 (m.d 0 2) (by simp) with h16072 | h16072
                                      · rcases p16060_3 (m.d 1 2) (by simp) with h16073 | h16073
                                        · rcases p16060_3 (m.d 2 3) (by simp) with h16074 | h16074
                                          · linarith only [h15535, h16074, hlam]
                                          · rcases p16060_3 (m.d 2 4) (by simp) with h16076 | h16076
                                            · linarith only [h16076, hlam, p16060_0]
                                            · rcases p16060_3 (m.d 2 5) (by simp) with h16078 | h16078
                                              · linarith only [h15537, h16078, hlam]
                                              · rcases h3bigk with h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c | h16080c
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [hlam, p16080_0]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [h15538, h16015, h16024, h16026, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p16080_1]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [h15538, h16024, h16026, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p16080_1]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [h15538, hlam, p16080_0]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  rcases p16080_3 (m.d 0 3) (by simp) with h16085 | h16085
                                                  · rcases p16080_3 (m.d 1 3) (by simp) with h16086 | h16086
                                                    · linarith only [h15532, h16086, hlam]
                                                    · linarith only [h16020, h16086, hlam]
                                                  · linarith only [h16085, hlam, p16080_0]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [h15532, hlam, p16080_0]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [hlam, p16080_0]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [h0, h15532, h16024, h16026, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16080_1]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [h16018, hlam, p16080_0]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [h0, h15533, h16018, h16026, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16080_1]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [h15535, hlam, p16080_0]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [h16015, hlam, p16080_0]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [hlam, p16080_0]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [h16022, hlam, p16080_0]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [h0, h15533, h16015, h16018, h16026, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16080_1]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [h15534, h16017, h16024, h16026, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p16027_1, p16080_1]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  rcases p16080_3 (m.d 0 3) (by simp) with h16101 | h16101
                                                  · linarith only [h15538, h16101, hlam]
                                                  · linarith only [h15532, h16101, hlam]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  rcases p16080_3 (m.d 0 3) (by simp) with h16104 | h16104
                                                  · linarith only [h15538, h16104, hlam]
                                                  · linarith only [h15535, h16104, hlam]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [hlam, p16080_0]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [h15534, h15538, h16017, h16024, hlam, p16027_1, p16080_2]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [h16013, hlam, p16080_0]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [h16020, hlam, p16080_0]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [h16024, hlam, p16080_0]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [h16026, hlam, p16080_0]
                                                · have p16080_0 := h16080c.1
                                                  have p16080_1 := h16080c.2.1
                                                  have p16080_2 := h16080c.2.2.1
                                                  have p16080_3 := h16080c.2.2.2
                                                  linarith only [hlam, p16080_0]
                                        · linarith only [h16016, h16073, hlam]
                                      · linarith only [h16072, hlam, p16060_0]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      rcases p16060_3 (m.d 0 2) (by simp) with h16116 | h16116
                                      · rcases p16060_3 (m.d 1 2) (by simp) with h16117 | h16117
                                        · rcases p16060_3 (m.d 2 3) (by simp) with h16118 | h16118
                                          · linarith only [h15535, h16118, hlam]
                                          · linarith only [h16024, h16118, hlam]
                                        · linarith only [h16017, h16117, hlam]
                                      · linarith only [h16116, hlam, p16060_0]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [h0, h15532, h15534, h16017, h16024, h16026, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16027_1, p16060_1]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [hlam, p16060_0]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      rcases p16060_3 (m.d 0 2) (by simp) with h16125 | h16125
                                      · linarith only [h0, h16125, hlam]
                                      · linarith only [h15535, h16125, hlam]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      rcases p16060_3 (m.d 0 2) (by simp) with h16128 | h16128
                                      · linarith only [h0, h16128, hlam]
                                      · linarith only [h15536, h16128, hlam]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [h0, h15533, h15534, h15538, h16017, hlam, p16027_1, p16060_2]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [h15535, hlam, p16060_0]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [h16015, hlam, p16060_0]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [hlam, p16060_0]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [h16022, hlam, p16060_0]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [h0, h15533, h16015, h16018, h16024, h16026, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16060_1]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [h15536, hlam, p16060_0]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [h16016, hlam, p16060_0]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [h0, h15533, h16016, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16060_1]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [hlam, p16060_0]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [h0, h15533, h16016, h16024, h16026, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16060_1]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [h15537, hlam, p16060_0]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [h16017, hlam, p16060_0]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [h16024, hlam, p16060_1]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [h16025, hlam, p16060_0]
                                    · have p16060_0 := h16060c.1
                                      have p16060_1 := h16060c.2.1
                                      have p16060_2 := h16060c.2.2.1
                                      have p16060_3 := h16060c.2.2.2
                                      linarith only [hlam, p16060_0]
                                · linarith only [h16014, h16057, hlam]
                              · linarith only [h16013, h16056, hlam]
                            · linarith only [h15537, h16055, hlam]
                          · linarith only [h15534, h16054, hlam]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [h15533, hlam, p16027_0]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [h15536, hlam, p16027_0]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [h0, h15533, h15535, h16024, h16026, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16027_1]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [hlam, p16027_0]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          rcases p16027_3 (m.d 0 1) (by simp) with h16155 | h16155
                          · rcases p16027_3 (m.d 0 2) (by simp) with h16156 | h16156
                            · rcases p16027_3 (m.d 0 3) (by simp) with h16157 | h16157
                              · linarith only [h15538, h16157, hlam]
                              · linarith only [h16013, h16157, hlam]
                            · linarith only [h15537, h16156, hlam]
                          · linarith only [h15534, h16155, hlam]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [h15534, hlam, p16027_0]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [h15537, hlam, p16027_1]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [h16013, hlam, p16027_0]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [h16014, hlam, p16027_1]
                        · have p16027_0 := h16027c.1
                          have p16027_1 := h16027c.2.1
                          have p16027_2 := h16027c.2.2.1
                          have p16027_3 := h16027c.2.2.2
                          linarith only [hlam, p16027_0]
                      · linarith only [h15538, h16014, h16026, hlam]
                    · linarith only [h0, h15533, h16021, h16025, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h15538, h16013, h16024, hc23, hc34, hlam, hphi]
              · linarith only [h0, h15533, h16014, h16018, h16020, h16021, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h15538, h16013, h16015, h16020, hc23, hc34, hlam, hphi]
        · linarith only [h0, h15533, h15537, h16014, h16017, hc02, hc45, hlam, hphi, ht0b, ht5b]
      · linarith only [h0, h15536, h16016, hlam]
    · linarith only [h0, h15535, h16015, hlam]
  · linarith only [h15538, h16013, h16014, hlam]

end R2N4
