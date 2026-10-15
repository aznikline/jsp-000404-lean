import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11016000 in
set_option maxHeartbeats 11016000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s16_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h19110 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h22593 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h16563 := hg16563
  have h17994 := hg17994
  rcases m.htr 0 2 5 (by decide) (by decide) with h22594 | h22594
  · rcases m.htr 0 3 4 (by decide) (by decide) with h22595 | h22595
    · rcases m.htr 0 3 5 (by decide) (by decide) with h22596 | h22596
      · rcases m.htr 0 4 5 (by decide) (by decide) with h22597 | h22597
        · rcases m.htr 1 2 3 (by decide) (by decide) with h22598 | h22598
          · rcases m.htr 1 2 4 (by decide) (by decide) with h22599 | h22599
            · rcases m.htr 1 2 5 (by decide) (by decide) with h22600 | h22600
              · rcases m.htr 1 3 4 (by decide) (by decide) with h22601 | h22601
                · rcases m.htr 1 3 5 (by decide) (by decide) with h22602 | h22602
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h22603 | h22603
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h22604 | h22604
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h22605 | h22605
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h22606 | h22606
                          · linarith only [h19110, h22593, h22598, h22606, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h19110, h22593, h22597, h22598, h22606, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h19110, h22594, h22596, h22605, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h19110, h22595, h22604, hlam]
                    · linarith only [h19110, h22593, h22597, h22598, h22603, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h19110, h22593, h22596, h22597, h22598, h22602, hlam]
                · linarith only [h19110, h22593, h22595, h22598, h22601, hlam]
              · linarith only [h19110, h22594, h22598, h22600, hlam]
            · linarith only [h19110, h22593, h22598, h22599, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h22616 | h22616
            · rcases m.htr 1 2 5 (by decide) (by decide) with h22617 | h22617
              · rcases m.htr 1 3 4 (by decide) (by decide) with h22618 | h22618
                · rcases m.htr 1 3 5 (by decide) (by decide) with h22619 | h22619
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h22620 | h22620
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h22621 | h22621
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h22622 | h22622
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h22623 | h22623
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h22624 | h22624
                            · rcases h1bigk with h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c | h22625c
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [hlam, p22625_0]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h0, hlam, p22625_0]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h14799, hlam, p22625_0]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h16563, hlam, p22625_0]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h17994, hlam, p22625_0]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h22598, hc01, hc23, hlam, hphi, ht12, p22625_1]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [hlam, p22625_0]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h22598, hlam, p22625_0]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h16563, h22598, hc01, hc23, hlam, hphi, ht12, p22625_1]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h17994, h22598, hc01, hc23, hlam, hphi, ht12, p22625_1]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                rcases p22625_3 (m.d 0 1) (by simp) with h22636 | h22636
                                · linarith only [h22636, hlam, p22625_0]
                                · rcases p22625_3 (m.d 1 2) (by simp) with h22638 | h22638
                                  · linarith only [h22598, h22638, hlam]
                                  · linarith only [h0, h22638, hlam]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h0, h22598, hc01, hc23, hlam, hphi, ht12, p22625_1]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [hlam, p22625_0]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h17994, h22598, h22620, hc01, hc23, hlam, hphi, ht12, p22625_1]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h17994, h22598, hc01, hc23, hlam, hphi, ht12, p22625_1]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h22598, h22616, hc01, hc23, hlam, hphi, ht12, p22625_1]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h22616, hlam, p22625_1]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h22618, hlam, p22625_0]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [hlam, p22625_0]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h17994, h22598, h22616, hc01, hc23, hlam, hphi, ht12, p22625_1]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h22598, h22617, hc01, hc23, hlam, hphi, ht12, p22625_1]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h22617, hlam, p22625_1]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h22619, hlam, p22625_0]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [h22620, hlam, p22625_0]
                              · have p22625_0 := h22625c.1
                                have p22625_1 := h22625c.2.1
                                have p22625_2 := h22625c.2.2.1
                                have p22625_3 := h22625c.2.2.2
                                linarith only [hlam, p22625_0]
                            · linarith only [h0, h22593, h22598, h22623, h22624, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h22656 | h22656
                            · linarith only [h22621, h22623, h22656, hlam]
                            · rcases h1bigk with h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c | h22658c
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [hlam, p22658_0]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h0, hlam, p22658_0]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h14799, hlam, p22658_0]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h16563, hlam, p22658_0]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h17994, hlam, p22658_0]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h22598, hc01, hc23, hlam, hphi, ht12, p22658_1]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [hlam, p22658_0]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h22598, hlam, p22658_0]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h16563, h22598, hc01, hc23, hlam, hphi, ht12, p22658_1]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h17994, h22598, hc01, hc23, hlam, hphi, ht12, p22658_1]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                rcases p22658_3 (m.d 0 1) (by simp) with h22669 | h22669
                                · linarith only [h22669, hlam, p22658_0]
                                · rcases p22658_3 (m.d 1 2) (by simp) with h22671 | h22671
                                  · linarith only [h22598, h22671, hlam]
                                  · linarith only [h0, h22671, hlam]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h0, h22598, hc01, hc23, hlam, hphi, ht12, p22658_1]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [hlam, p22658_0]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h16563, h22597, h22598, h22621, h22623, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p22658_1]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h17994, h22598, hc01, hc23, hlam, hphi, ht12, p22658_1]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h22598, h22616, hc01, hc23, hlam, hphi, ht12, p22658_1]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h22616, hlam, p22658_1]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h22618, hlam, p22658_0]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [hlam, p22658_0]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h17994, h22598, h22616, hc01, hc23, hlam, hphi, ht12, p22658_1]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h22598, h22617, hc01, hc23, hlam, hphi, ht12, p22658_1]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h22617, hlam, p22658_1]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h22619, hlam, p22658_0]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [h22620, hlam, p22658_0]
                              · have p22658_0 := h22658c.1
                                have p22658_1 := h22658c.2.1
                                have p22658_2 := h22658c.2.2.1
                                have p22658_3 := h22658c.2.2.2
                                linarith only [hlam, p22658_0]
                        · linarith only [h0, h22598, h22622, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h22598, h22621, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h16563, h22597, h22620, hlam]
                  · linarith only [h14799, h22596, h22619, hlam]
                · linarith only [h14799, h22595, h22618, hlam]
              · linarith only [h0, h22594, h22617, hlam]
            · linarith only [h0, h22593, h22616, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h22695 | h22695
          · rcases m.htr 1 2 4 (by decide) (by decide) with h22696 | h22696
            · rcases m.htr 1 2 5 (by decide) (by decide) with h22697 | h22697
              · rcases m.htr 1 3 4 (by decide) (by decide) with h22698 | h22698
                · rcases m.htr 1 3 5 (by decide) (by decide) with h22699 | h22699
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h22700 | h22700
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h22701 | h22701
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h22702 | h22702
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h22703 | h22703
                          · linarith only [h19110, h22593, h22597, h22695, h22703, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h22705 | h22705
                            · linarith only [h16563, h19110, h22594, h22597, h22695, h22701, h22703, h22705, hc01, hc12, hlam, hphi]
                            · rcases h1bigk with h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c | h22707c
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [hlam, p22707_0]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [h0, hlam, p22707_0]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [h14799, hlam, p22707_0]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [h16563, hlam, p22707_0]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [h17994, hlam, p22707_0]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                rcases p22707_3 (m.d 0 1) (by simp) with h22713 | h22713
                                · linarith only [h22713, hlam, p22707_0]
                                · rcases p22707_3 (m.d 1 2) (by simp) with h22715 | h22715
                                  · rcases p22707_3 (m.d 1 3) (by simp) with h22716 | h22716
                                    · linarith only [h22695, h22716, hlam]
                                    · linarith only [h14799, h22716, hlam]
                                  · linarith only [h22715, hlam, p22707_0]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [hlam, p22707_0]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [h16563, h22597, h22698, h22700, hc01, hc12, hlam, hphi, p22707_1]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [h16563, h22597, h22700, hc01, hc12, hlam, hphi, p22707_1]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [h16563, h22597, h22700, hc01, hc12, hlam, hphi, p22707_1]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                rcases p22707_3 (m.d 0 1) (by simp) with h22724 | h22724
                                · linarith only [h22724, hlam, p22707_0]
                                · rcases p22707_3 (m.d 1 2) (by simp) with h22726 | h22726
                                  · rcases p22707_3 (m.d 1 3) (by simp) with h22727 | h22727
                                    · rcases p22707_3 (m.d 1 4) (by simp) with h22728 | h22728
                                      · linarith only [h22698, h22728, hlam]
                                      · linarith only [h16563, h22728, hlam]
                                    · linarith only [h22727, hlam, p22707_0]
                                  · linarith only [h0, h22726, hlam]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [h22695, hlam, p22707_1]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [hlam, p22707_0]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [h16563, h22597, h22700, hc01, hc13, hlam, hphi, p22707_1]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [h16563, h22597, h22695, h22700, hc01, hc12, hlam, hphi, p22707_1]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                rcases p22707_3 (m.d 0 1) (by simp) with h22737 | h22737
                                · linarith only [h22737, hlam, p22707_0]
                                · rcases p22707_3 (m.d 1 2) (by simp) with h22739 | h22739
                                  · rcases p22707_3 (m.d 1 3) (by simp) with h22740 | h22740
                                    · rcases p22707_3 (m.d 1 4) (by simp) with h22741 | h22741
                                      · rcases p22707_3 (m.d 1 5) (by simp) with h22742 | h22742
                                        · linarith only [h22700, h22742, hlam]
                                        · linarith only [h17994, h22742, hlam]
                                      · linarith only [h22741, hlam, p22707_0]
                                    · linarith only [h14799, h22740, hlam]
                                  · linarith only [h0, h22739, hlam]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [h22696, hlam, p22707_1]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [h22698, hlam, p22707_0]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [hlam, p22707_0]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [h16563, h22597, h22700, hc01, hc14, hlam, hphi, p22707_1]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                rcases p22707_3 (m.d 0 1) (by simp) with h22752 | h22752
                                · linarith only [h22752, hlam, p22707_0]
                                · rcases p22707_3 (m.d 1 2) (by simp) with h22754 | h22754
                                  · rcases p22707_3 (m.d 1 3) (by simp) with h22755 | h22755
                                    · rcases p22707_3 (m.d 1 4) (by simp) with h22756 | h22756
                                      · rcases p22707_3 (m.d 1 5) (by simp) with h22757 | h22757
                                        · rcases h3bigk with h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c | h22758c
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [hlam, p22758_0]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [h14799, hlam, p22758_1]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [h19110, hlam, p22758_1]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            rcases p22758_3 (m.d 0 3) (by simp) with h22762 | h22762
                                            · rcases p22758_3 (m.d 1 3) (by simp) with h22763 | h22763
                                              · rcases p22758_3 (m.d 2 3) (by simp) with h22764 | h22764
                                                · rcases p22758_3 (m.d 3 4) (by simp) with h22765 | h22765
                                                  · linarith only [h22765, hlam, p22758_0]
                                                  · rcases p22758_3 (m.d 3 5) (by simp) with h22767 | h22767
                                                    · linarith only [h22596, h22767, hlam]
                                                    · linarith only [h22705, h22767, hlam]
                                                · linarith only [h22701, h22764, hlam]
                                              · linarith only [h22698, h22763, hlam]
                                            · linarith only [h22762, hlam, p22758_0]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            rcases p22758_3 (m.d 0 3) (by simp) with h22773 | h22773
                                            · rcases p22758_3 (m.d 1 3) (by simp) with h22774 | h22774
                                              · rcases p22758_3 (m.d 2 3) (by simp) with h22775 | h22775
                                                · rcases p22758_3 (m.d 3 4) (by simp) with h22776 | h22776
                                                  · linarith only [h22595, h22776, hlam]
                                                  · rcases p22758_3 (m.d 3 5) (by simp) with h22778 | h22778
                                                    · linarith only [h22778, hlam, p22758_0]
                                                    · rcases h5bigk with h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c | h22780c
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [hlam, p22780_0]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h17994, hlam, p22780_1]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h19110, h22594, h22695, h22703, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p22780_1]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h19110, h22594, h22695, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p22780_1]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h22597, hlam, p22780_1]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h17994, hc01, hc15, hlam, hphi, p22780_1]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [hlam, p22780_0]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        rcases p22780_3 (m.d 0 5) (by simp) with h22788 | h22788
                                                        · linarith only [h17994, h22788, hlam]
                                                        · linarith only [h22594, h22788, hlam]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        rcases p22780_3 (m.d 0 5) (by simp) with h22791 | h22791
                                                        · linarith only [h17994, h22791, hlam]
                                                        · linarith only [h22596, h22791, hlam]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h16563, h22597, h22695, h22698, h22700, hc01, hc12, hlam, hphi, p22780_1]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h22594, hlam, p22780_1]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h22697, hlam, p22780_1]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [hlam, p22780_0]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h19110, h22594, h22695, h22705, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22780_1]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h22703, hlam, p22780_1]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h22596, hlam, p22780_0]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h22699, hlam, p22780_0]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h22702, hlam, p22780_0]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [hlam, p22780_0]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h22705, hlam, p22780_1]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h16563, h22597, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p22780_1]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h22700, hlam, p22780_0]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h22695, h22698, h22700, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p22780_1]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [h22695, h22698, h22700, h22705, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22780_1]
                                                      · have p22780_0 := h22780c.1
                                                        have p22780_1 := h22780c.2.1
                                                        have p22780_2 := h22780c.2.2.1
                                                        have p22780_3 := h22780c.2.2.2
                                                        linarith only [hlam, p22780_0]
                                                · linarith only [h22702, h22775, hlam]
                                              · linarith only [h22699, h22774, hlam]
                                            · linarith only [h22773, hlam, p22758_0]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            rcases p22758_3 (m.d 0 3) (by simp) with h22813 | h22813
                                            · linarith only [h14799, h22813, hlam]
                                            · rcases p22758_3 (m.d 1 3) (by simp) with h22815 | h22815
                                              · rcases p22758_3 (m.d 2 3) (by simp) with h22816 | h22816
                                                · linarith only [h22695, h22816, hlam]
                                                · linarith only [h19110, h22816, hlam]
                                              · linarith only [h14799, h22815, hlam]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [hlam, p22758_0]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [h0, h19110, h22695, hc01, hc12, hlam, hphi, p22758_1]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            rcases p22758_3 (m.d 0 3) (by simp) with h22822 | h22822
                                            · linarith only [h14799, h22822, hlam]
                                            · linarith only [h22595, h22822, hlam]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            rcases p22758_3 (m.d 0 3) (by simp) with h22825 | h22825
                                            · linarith only [h14799, h22825, hlam]
                                            · linarith only [h22596, h22825, hlam]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [h19110, h22594, h22695, h22702, h22705, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22758_1]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [h22695, hlam, p22758_0]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [hlam, p22758_0]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            rcases p22758_3 (m.d 0 3) (by simp) with h22831 | h22831
                                            · linarith only [h19110, h22831, hlam]
                                            · linarith only [h22595, h22831, hlam]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            rcases p22758_3 (m.d 0 3) (by simp) with h22834 | h22834
                                            · linarith only [h19110, h22834, hlam]
                                            · linarith only [h22596, h22834, hlam]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [h22595, hlam, p22758_0]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [h22698, hlam, p22758_0]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [h22701, hlam, p22758_0]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [hlam, p22758_0]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [h22705, hlam, p22758_1]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [h22596, hlam, p22758_0]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [h22699, hlam, p22758_0]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [h22702, hlam, p22758_0]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [h19110, h22594, h22695, h22702, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22758_1]
                                          · have p22758_0 := h22758c.1
                                            have p22758_1 := h22758c.2.1
                                            have p22758_2 := h22758c.2.2.1
                                            have p22758_3 := h22758c.2.2.2
                                            linarith only [hlam, p22758_0]
                                        · linarith only [h22757, hlam, p22707_0]
                                      · linarith only [h16563, h22756, hlam]
                                    · linarith only [h14799, h22755, hlam]
                                  · linarith only [h0, h22754, hlam]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [h22697, hlam, p22707_1]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [h22699, hlam, p22707_0]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [h22700, hlam, p22707_0]
                              · have p22707_0 := h22707c.1
                                have p22707_1 := h22707c.2.1
                                have p22707_2 := h22707c.2.2.1
                                have p22707_3 := h22707c.2.2.2
                                linarith only [hlam, p22707_0]
                        · linarith only [h19110, h22594, h22596, h22702, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h19110, h22595, h22701, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h22857 | h22857
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h22858 | h22858
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h22859 | h22859
                          · linarith only [h19110, h22593, h22700, h22859, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h22861 | h22861
                            · linarith only [h16563, h22700, h22861, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h1bigk with h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c | h22863c
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [hlam, p22863_0]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [h0, hlam, p22863_0]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [h14799, hlam, p22863_0]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [h16563, hlam, p22863_0]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [h17994, hlam, p22863_0]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                rcases p22863_3 (m.d 0 1) (by simp) with h22869 | h22869
                                · linarith only [h22869, hlam, p22863_0]
                                · rcases p22863_3 (m.d 1 2) (by simp) with h22871 | h22871
                                  · rcases p22863_3 (m.d 1 3) (by simp) with h22872 | h22872
                                    · linarith only [h22695, h22872, hlam]
                                    · linarith only [h14799, h22872, hlam]
                                  · linarith only [h22871, hlam, p22863_0]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [hlam, p22863_0]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [h14799, hc01, hc12, hlam, hphi, p22863_1]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [h16563, hc01, hc12, hlam, hphi, p22863_1]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [h16563, h22700, hc01, hc12, hlam, hphi, p22863_1]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                rcases p22863_3 (m.d 0 1) (by simp) with h22880 | h22880
                                · linarith only [h22880, hlam, p22863_0]
                                · rcases p22863_3 (m.d 1 2) (by simp) with h22882 | h22882
                                  · rcases p22863_3 (m.d 1 3) (by simp) with h22883 | h22883
                                    · rcases p22863_3 (m.d 1 4) (by simp) with h22884 | h22884
                                      · linarith only [h22698, h22884, hlam]
                                      · linarith only [h16563, h22884, hlam]
                                    · linarith only [h22883, hlam, p22863_0]
                                  · linarith only [h0, h22882, hlam]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [h22695, hlam, p22863_1]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [hlam, p22863_0]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [h16563, hc01, hc13, hlam, hphi, p22863_1]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [h16563, h22695, h22700, hc01, hc12, hlam, hphi, p22863_1]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [h22700, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p22863_1]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [h22696, hlam, p22863_1]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [h22698, hlam, p22863_0]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [hlam, p22863_0]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [h22700, hlam, p22863_1]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                rcases p22863_3 (m.d 0 1) (by simp) with h22898 | h22898
                                · linarith only [h22898, hlam, p22863_0]
                                · rcases p22863_3 (m.d 1 2) (by simp) with h22900 | h22900
                                  · rcases p22863_3 (m.d 1 3) (by simp) with h22901 | h22901
                                    · rcases p22863_3 (m.d 1 4) (by simp) with h22902 | h22902
                                      · linarith only [h22700, h22902, hlam]
                                      · linarith only [h16563, h22902, hlam]
                                    · linarith only [h14799, h22901, hlam]
                                  · linarith only [h0, h22900, hlam]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [h22697, hlam, p22863_1]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [h22699, hlam, p22863_0]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [h16563, hc01, hc15, hlam, hphi, p22863_1]
                              · have p22863_0 := h22863c.1
                                have p22863_1 := h22863c.2.1
                                have p22863_2 := h22863c.2.2.1
                                have p22863_3 := h22863c.2.2.2
                                linarith only [hlam, p22863_0]
                        · linarith only [h19110, h22596, h22858, hlam]
                      · linarith only [h19110, h22595, h22857, hlam]
                  · linarith only [h14799, h19110, h22594, h22596, h22699, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h19110, h22593, h22595, h22695, h22698, hlam]
              · linarith only [h19110, h22594, h22695, h22697, hlam]
            · linarith only [h19110, h22695, h22696, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h22917 | h22917
            · rcases m.htr 1 2 5 (by decide) (by decide) with h22918 | h22918
              · rcases m.htr 1 3 4 (by decide) (by decide) with h22919 | h22919
                · rcases m.htr 1 3 5 (by decide) (by decide) with h22920 | h22920
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h22921 | h22921
                    · linarith only [h16563, h22597, h22695, h22917, h22921, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h22923 | h22923
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h22924 | h22924
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h22925 | h22925
                          · linarith only [h0, h22593, h22695, h22921, h22925, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h22927 | h22927
                            · linarith only [h16563, h22921, h22927, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h1bigk with h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c | h22929c
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [hlam, p22929_0]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h0, hlam, p22929_0]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h14799, hlam, p22929_0]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h16563, hlam, p22929_0]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h17994, hlam, p22929_0]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h22695, hc01, hc23, hlam, hphi, ht12, p22929_1]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [hlam, p22929_0]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h22695, hlam, p22929_0]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h16563, h22695, hc01, hc23, hlam, hphi, ht12, p22929_1]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h17994, h22695, hc01, hc23, hlam, hphi, ht12, p22929_1]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                rcases p22929_3 (m.d 0 1) (by simp) with h22940 | h22940
                                · linarith only [h22940, hlam, p22929_0]
                                · rcases p22929_3 (m.d 1 2) (by simp) with h22942 | h22942
                                  · linarith only [h22695, h22942, hlam]
                                  · linarith only [h0, h22942, hlam]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h0, h22695, hc01, hc23, hlam, hphi, ht12, p22929_1]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [hlam, p22929_0]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h16563, h22695, hc01, hc23, hlam, hphi, ht12, p22929_1]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h16563, h22695, h22921, hc01, hc23, hlam, hphi, ht12, p22929_1]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h22921, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p22929_1]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h22917, hlam, p22929_1]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h22919, hlam, p22929_0]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [hlam, p22929_0]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h22921, hlam, p22929_1]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h22695, h22918, hc01, hc23, hlam, hphi, ht12, p22929_1]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h22918, hlam, p22929_1]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h22920, hlam, p22929_0]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [h16563, h22695, h22918, hc01, hc23, hlam, hphi, ht12, p22929_1]
                              · have p22929_0 := h22929c.1
                                have p22929_1 := h22929c.2.1
                                have p22929_2 := h22929c.2.2.1
                                have p22929_3 := h22929c.2.2.2
                                linarith only [hlam, p22929_0]
                        · linarith only [h0, h22695, h22924, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h22695, h22923, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h14799, h22596, h22920, hlam]
                · linarith only [h14799, h22595, h22919, hlam]
              · linarith only [h0, h22594, h22918, hlam]
            · linarith only [h0, h22593, h22917, hlam]
      · linarith only [h19110, h22594, h22596, hlam]
    · linarith only [h19110, h22593, h22595, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h22967 | h22967
    · rcases m.htr 0 3 5 (by decide) (by decide) with h22968 | h22968
      · rcases m.htr 0 4 5 (by decide) (by decide) with h22969 | h22969
        · linarith only [h22593, h22594, h22969, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h22971 | h22971
          · rcases m.htr 1 2 4 (by decide) (by decide) with h22972 | h22972
            · rcases m.htr 1 2 5 (by decide) (by decide) with h22973 | h22973
              · rcases m.htr 1 3 4 (by decide) (by decide) with h22974 | h22974
                · rcases m.htr 1 3 5 (by decide) (by decide) with h22975 | h22975
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h22976 | h22976
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h22977 | h22977
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h22978 | h22978
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h22979 | h22979
                          · linarith only [h16563, h22593, h22594, h22969, h22973, h22979, hc01, hc15, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h22981 | h22981
                            · linarith only [h22593, h22594, h22977, h22979, h22981, hlam]
                            · rcases h1bigk with h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c | h22983c
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [hlam, p22983_0]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [h0, hlam, p22983_0]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [h14799, hlam, p22983_0]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [h16563, hlam, p22983_0]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [h17994, hlam, p22983_0]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                rcases p22983_3 (m.d 0 1) (by simp) with h22989 | h22989
                                · linarith only [h22989, hlam, p22983_0]
                                · rcases p22983_3 (m.d 1 2) (by simp) with h22991 | h22991
                                  · rcases p22983_3 (m.d 1 3) (by simp) with h22992 | h22992
                                    · linarith only [h22971, h22992, hlam]
                                    · linarith only [h14799, h22992, hlam]
                                  · linarith only [h22991, hlam, p22983_0]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [hlam, p22983_0]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [h14799, hc01, hc12, hlam, hphi, p22983_1]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [h22593, h22594, h22976, h22977, h22979, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22983_1]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [h17994, hc01, hc12, hlam, hphi, p22983_1]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                rcases p22983_3 (m.d 0 1) (by simp) with h23000 | h23000
                                · linarith only [h23000, hlam, p22983_0]
                                · rcases p22983_3 (m.d 1 2) (by simp) with h23002 | h23002
                                  · rcases p22983_3 (m.d 1 3) (by simp) with h23003 | h23003
                                    · rcases p22983_3 (m.d 1 4) (by simp) with h23004 | h23004
                                      · linarith only [h22974, h23004, hlam]
                                      · linarith only [h16563, h23004, hlam]
                                    · linarith only [h23003, hlam, p22983_0]
                                  · linarith only [h0, h23002, hlam]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [h22971, hlam, p22983_1]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [hlam, p22983_0]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [h22593, h22594, h22976, h22977, h22979, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22983_1]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [h22593, h22594, h22971, h22976, h22977, h22979, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22983_1]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                rcases p22983_3 (m.d 0 1) (by simp) with h23013 | h23013
                                · linarith only [h23013, hlam, p22983_0]
                                · rcases p22983_3 (m.d 1 2) (by simp) with h23015 | h23015
                                  · rcases p22983_3 (m.d 1 3) (by simp) with h23016 | h23016
                                    · rcases p22983_3 (m.d 1 4) (by simp) with h23017 | h23017
                                      · rcases p22983_3 (m.d 1 5) (by simp) with h23018 | h23018
                                        · linarith only [h22976, h23018, hlam]
                                        · linarith only [h17994, h23018, hlam]
                                      · linarith only [h23017, hlam, p22983_0]
                                    · linarith only [h14799, h23016, hlam]
                                  · linarith only [h0, h23015, hlam]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [h22972, hlam, p22983_1]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [h22974, hlam, p22983_0]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [hlam, p22983_0]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [h22593, h22594, h22976, h22977, h22979, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22983_1]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                rcases p22983_3 (m.d 0 1) (by simp) with h23028 | h23028
                                · linarith only [h23028, hlam, p22983_0]
                                · rcases p22983_3 (m.d 1 2) (by simp) with h23030 | h23030
                                  · rcases p22983_3 (m.d 1 3) (by simp) with h23031 | h23031
                                    · rcases p22983_3 (m.d 1 4) (by simp) with h23032 | h23032
                                      · rcases p22983_3 (m.d 1 5) (by simp) with h23033 | h23033
                                        · rcases h3bigk with h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c | h23034c
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [hlam, p23034_0]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [h14799, hlam, p23034_1]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [h19110, hlam, p23034_1]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            rcases p23034_3 (m.d 0 3) (by simp) with h23038 | h23038
                                            · rcases p23034_3 (m.d 1 3) (by simp) with h23039 | h23039
                                              · rcases p23034_3 (m.d 2 3) (by simp) with h23040 | h23040
                                                · rcases p23034_3 (m.d 3 4) (by simp) with h23041 | h23041
                                                  · linarith only [h23041, hlam, p23034_0]
                                                  · rcases p23034_3 (m.d 3 5) (by simp) with h23043 | h23043
                                                    · linarith only [h22968, h23043, hlam]
                                                    · linarith only [h22981, h23043, hlam]
                                                · linarith only [h22977, h23040, hlam]
                                              · linarith only [h22974, h23039, hlam]
                                            · linarith only [h23038, hlam, p23034_0]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            rcases p23034_3 (m.d 0 3) (by simp) with h23049 | h23049
                                            · rcases p23034_3 (m.d 1 3) (by simp) with h23050 | h23050
                                              · rcases p23034_3 (m.d 2 3) (by simp) with h23051 | h23051
                                                · rcases p23034_3 (m.d 3 4) (by simp) with h23052 | h23052
                                                  · linarith only [h22967, h23052, hlam]
                                                  · rcases p23034_3 (m.d 3 5) (by simp) with h23054 | h23054
                                                    · linarith only [h23054, hlam, p23034_0]
                                                    · rcases h5bigk with h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c | h23056c
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [hlam, p23056_0]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h17994, hlam, p23056_1]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h22594, hlam, p23056_0]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h19110, h22968, h22971, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p23056_1]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h22969, hlam, p23056_1]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h17994, hc01, hc15, hlam, hphi, p23056_1]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [hlam, p23056_0]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h22593, h22594, h22973, h22977, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23056_1]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        rcases p23056_3 (m.d 0 5) (by simp) with h23065 | h23065
                                                        · linarith only [h17994, h23065, hlam]
                                                        · linarith only [h22968, h23065, hlam]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h22593, h22594, h22971, h22974, h22976, h22977, h22979, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23056_1]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h22593, h22594, h22977, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p23056_1]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h22973, hlam, p23056_1]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [hlam, p23056_0]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h22971, h22978, h22981, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23056_1]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h22979, hlam, p23056_1]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h22968, hlam, p23056_0]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h22975, hlam, p23056_0]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h22978, hlam, p23056_0]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [hlam, p23056_0]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h22981, hlam, p23056_1]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h22593, h22594, h22971, h22974, h22976, h22977, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23056_1]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h22976, hlam, p23056_0]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h22971, h22974, h22976, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p23056_1]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [h22971, h22974, h22976, h22981, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23056_1]
                                                      · have p23056_0 := h23056c.1
                                                        have p23056_1 := h23056c.2.1
                                                        have p23056_2 := h23056c.2.2.1
                                                        have p23056_3 := h23056c.2.2.2
                                                        linarith only [hlam, p23056_0]
                                                · linarith only [h22978, h23051, hlam]
                                              · linarith only [h22975, h23050, hlam]
                                            · linarith only [h23049, hlam, p23034_0]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            rcases p23034_3 (m.d 0 3) (by simp) with h23087 | h23087
                                            · linarith only [h14799, h23087, hlam]
                                            · rcases p23034_3 (m.d 1 3) (by simp) with h23089 | h23089
                                              · rcases p23034_3 (m.d 2 3) (by simp) with h23090 | h23090
                                                · linarith only [h22971, h23090, hlam]
                                                · linarith only [h19110, h23090, hlam]
                                              · linarith only [h14799, h23089, hlam]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [hlam, p23034_0]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [h19110, h22593, h22971, h22977, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23034_1]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [h22593, h22594, h22974, h22976, h22977, h22979, hlam, p23034_2]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            rcases p23034_3 (m.d 0 3) (by simp) with h23097 | h23097
                                            · linarith only [h14799, h23097, hlam]
                                            · linarith only [h22968, h23097, hlam]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [h22968, h22971, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p23034_1]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [h22971, hlam, p23034_0]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [hlam, p23034_0]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            rcases p23034_3 (m.d 0 3) (by simp) with h23103 | h23103
                                            · linarith only [h19110, h23103, hlam]
                                            · linarith only [h22967, h23103, hlam]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            rcases p23034_3 (m.d 0 3) (by simp) with h23106 | h23106
                                            · linarith only [h19110, h23106, hlam]
                                            · linarith only [h22968, h23106, hlam]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [h22967, hlam, p23034_0]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [h22974, hlam, p23034_0]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [h22977, hlam, p23034_0]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [hlam, p23034_0]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [h22981, hlam, p23034_1]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [h22968, hlam, p23034_0]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [h22975, hlam, p23034_0]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [h22978, hlam, p23034_0]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [h19110, h22968, h22971, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23034_1]
                                          · have p23034_0 := h23034c.1
                                            have p23034_1 := h23034c.2.1
                                            have p23034_2 := h23034c.2.2.1
                                            have p23034_3 := h23034c.2.2.2
                                            linarith only [hlam, p23034_0]
                                        · linarith only [h23033, hlam, p22983_0]
                                      · linarith only [h16563, h23032, hlam]
                                    · linarith only [h14799, h23031, hlam]
                                  · linarith only [h0, h23030, hlam]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [h22973, hlam, p22983_1]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [h22975, hlam, p22983_0]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [h22976, hlam, p22983_0]
                              · have p22983_0 := h22983c.1
                                have p22983_1 := h22983c.2.1
                                have p22983_2 := h22983c.2.2.1
                                have p22983_3 := h22983c.2.2.2
                                linarith only [hlam, p22983_0]
                        · linarith only [h19110, h22968, h22978, hlam]
                      · linarith only [h19110, h22593, h22967, h22977, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h23129 | h23129
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h23130 | h23130
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h23131 | h23131
                          · linarith only [h22593, h22594, h22976, h23131, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h23133 | h23133
                            · linarith only [h16563, h22593, h22594, h22971, h22976, h23129, h23130, h23133, hc01, hc12, hlam, hphi]
                            · rcases h1bigk with h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c | h23135c
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [hlam, p23135_0]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [h0, hlam, p23135_0]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [h14799, hlam, p23135_0]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [h16563, hlam, p23135_0]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [h17994, hlam, p23135_0]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                rcases p23135_3 (m.d 0 1) (by simp) with h23141 | h23141
                                · linarith only [h23141, hlam, p23135_0]
                                · rcases p23135_3 (m.d 1 2) (by simp) with h23143 | h23143
                                  · rcases p23135_3 (m.d 1 3) (by simp) with h23144 | h23144
                                    · linarith only [h22971, h23144, hlam]
                                    · linarith only [h14799, h23144, hlam]
                                  · linarith only [h23143, hlam, p23135_0]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [hlam, p23135_0]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [h14799, hc01, hc12, hlam, hphi, p23135_1]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [h16563, hc01, hc12, hlam, hphi, p23135_1]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [h17994, hc01, hc12, hlam, hphi, p23135_1]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                rcases p23135_3 (m.d 0 1) (by simp) with h23152 | h23152
                                · linarith only [h23152, hlam, p23135_0]
                                · rcases p23135_3 (m.d 1 2) (by simp) with h23154 | h23154
                                  · rcases p23135_3 (m.d 1 3) (by simp) with h23155 | h23155
                                    · rcases p23135_3 (m.d 1 4) (by simp) with h23156 | h23156
                                      · linarith only [h22974, h23156, hlam]
                                      · linarith only [h16563, h23156, hlam]
                                    · linarith only [h23155, hlam, p23135_0]
                                  · linarith only [h0, h23154, hlam]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [h22971, hlam, p23135_1]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [hlam, p23135_0]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [h16563, hc01, hc13, hlam, hphi, p23135_1]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [h22593, h22594, h22971, h22973, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p23135_1]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [h22976, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p23135_1]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [h22972, hlam, p23135_1]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [h22974, hlam, p23135_0]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [hlam, p23135_0]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [h22976, hlam, p23135_1]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                rcases p23135_3 (m.d 0 1) (by simp) with h23170 | h23170
                                · linarith only [h23170, hlam, p23135_0]
                                · rcases p23135_3 (m.d 1 2) (by simp) with h23172 | h23172
                                  · rcases p23135_3 (m.d 1 3) (by simp) with h23173 | h23173
                                    · rcases p23135_3 (m.d 1 4) (by simp) with h23174 | h23174
                                      · linarith only [h22976, h23174, hlam]
                                      · linarith only [h16563, h23174, hlam]
                                    · linarith only [h14799, h23173, hlam]
                                  · linarith only [h0, h23172, hlam]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [h22973, hlam, p23135_1]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [h22975, hlam, p23135_0]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [h16563, hc01, hc15, hlam, hphi, p23135_1]
                              · have p23135_0 := h23135c.1
                                have p23135_1 := h23135c.2.1
                                have p23135_2 := h23135c.2.2.1
                                have p23135_3 := h23135c.2.2.2
                                linarith only [hlam, p23135_0]
                        · linarith only [h19110, h22593, h22968, h23129, h23130, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h19110, h22593, h22967, h23129, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h14799, h19110, h22968, h22975, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h19110, h22593, h22967, h22971, h22974, hlam]
              · linarith only [h19110, h22971, h22973, hc02, hc25, hlam, hphi]
            · linarith only [h19110, h22593, h22971, h22972, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h23189 | h23189
            · rcases m.htr 1 2 5 (by decide) (by decide) with h23190 | h23190
              · linarith only [h22593, h22594, h22971, h23190, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h23192 | h23192
                · rcases m.htr 1 3 5 (by decide) (by decide) with h23193 | h23193
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h23194 | h23194
                    · linarith only [h16563, h22969, h22971, h23189, h23194, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h23196 | h23196
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h23197 | h23197
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h23198 | h23198
                          · linarith only [h0, h22593, h23190, h23194, h23197, h23198, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h23200 | h23200
                            · linarith only [h0, h23190, h23198, h23200, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h1bigk with h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c | h23202c
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [hlam, p23202_0]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h0, hlam, p23202_0]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h14799, hlam, p23202_0]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h16563, hlam, p23202_0]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h17994, hlam, p23202_0]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h23190, h23197, hc01, hc23, hlam, hphi, ht12, p23202_1]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [hlam, p23202_0]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h22971, hlam, p23202_0]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h23190, h23198, hc14, hc45, hlam, hphi, p23202_1]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h23190, hlam, p23202_0]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                rcases p23202_3 (m.d 0 1) (by simp) with h23213 | h23213
                                · linarith only [h23213, hlam, p23202_0]
                                · rcases p23202_3 (m.d 1 2) (by simp) with h23215 | h23215
                                  · linarith only [h22971, h23215, hlam]
                                  · linarith only [h0, h23215, hlam]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h0, h22971, hc01, hc23, hlam, hphi, ht12, p23202_1]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [hlam, p23202_0]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h16563, h22971, hc01, hc23, hlam, hphi, ht12, p23202_1]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h17994, h22971, hc01, hc23, hlam, hphi, ht12, p23202_1]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h23189, h23190, hc01, hc25, hlam, hphi, ht12, p23202_1]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h23189, hlam, p23202_1]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h23192, hlam, p23202_0]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [hlam, p23202_0]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h23194, hlam, p23202_1]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                rcases p23202_3 (m.d 0 1) (by simp) with h23227 | h23227
                                · linarith only [h23227, hlam, p23202_0]
                                · rcases p23202_3 (m.d 1 2) (by simp) with h23229 | h23229
                                  · linarith only [h23190, h23229, hlam]
                                  · linarith only [h0, h23229, hlam]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p23202_1]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h23193, hlam, p23202_0]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [h16563, hc01, hc15, hlam, hphi, p23202_1]
                              · have p23202_0 := h23202c.1
                                have p23202_1 := h23202c.2.1
                                have p23202_2 := h23202c.2.2.1
                                have p23202_3 := h23202c.2.2.2
                                linarith only [hlam, p23202_0]
                        · linarith only [h14799, h22968, h22971, h23197, hlam]
                      · linarith only [h14799, h22967, h22971, h23196, hlam]
                  · linarith only [h14799, h22968, h23193, hlam]
                · linarith only [h14799, h16563, h22967, h22971, h23189, h23192, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h22593, h23189, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h23241 | h23241
        · linarith only [h22593, h22594, h23241, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h23243 | h23243
          · rcases m.htr 1 2 4 (by decide) (by decide) with h23244 | h23244
            · rcases m.htr 1 2 5 (by decide) (by decide) with h23245 | h23245
              · rcases m.htr 1 3 4 (by decide) (by decide) with h23246 | h23246
                · rcases m.htr 1 3 5 (by decide) (by decide) with h23247 | h23247
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h23248 | h23248
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h23249 | h23249
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h23250 | h23250
                        · linarith only [h14799, h22968, h23243, h23250, hc01, hc12, hlam, hphi]
                        · linarith only [h19110, h22593, h23243, h23247, h23249, h23250, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h19110, h22967, h23249, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h23254 | h23254
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h23255 | h23255
                        · linarith only [h14799, h22968, h23243, h23255, hc01, hc12, hlam, hphi]
                        · linarith only [h19110, h22593, h23243, h23247, h23254, h23255, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h19110, h22967, h23254, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h23259 | h23259
                    · linarith only [h16563, h23241, h23246, h23247, h23259, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h23261 | h23261
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h23262 | h23262
                        · linarith only [h23243, h23247, h23262, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h23264 | h23264
                          · linarith only [h0, h17994, h22593, h23259, h23264, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h23266 | h23266
                            · linarith only [h16563, h22593, h23259, h23261, h23266, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · linarith only [h19110, h22593, h23243, h23247, h23261, h23266, hc34, hc45, hlam, hphi]
                      · linarith only [h19110, h22967, h23261, hlam]
                · linarith only [h19110, h22593, h22967, h23243, h23246, hlam]
              · linarith only [h19110, h22593, h23243, h23245, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h19110, h22593, h23243, h23244, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h23273 | h23273
            · rcases m.htr 1 2 5 (by decide) (by decide) with h23274 | h23274
              · linarith only [h22593, h22594, h23243, h23274, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h23276 | h23276
                · rcases m.htr 1 3 5 (by decide) (by decide) with h23277 | h23277
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h23278 | h23278
                    · linarith only [h16563, h23241, h23243, h23273, h23278, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h23280 | h23280
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h23281 | h23281
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h23282 | h23282
                          · linarith only [h0, h17994, h22593, h23274, h23278, h23281, h23282, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h23284 | h23284
                            · linarith only [h16563, h22593, h23273, h23274, h23280, h23282, h23284, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · rcases h1bigk with h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c | h23286c
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [hlam, p23286_0]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h0, hlam, p23286_0]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h14799, hlam, p23286_0]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h16563, hlam, p23286_0]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h17994, hlam, p23286_0]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h23274, h23282, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p23286_1]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [hlam, p23286_0]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h23243, hlam, p23286_0]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h16563, h19110, h22593, h22968, h23243, h23274, h23277, h23280, h23282, hc01, hc23, hc34, hc45, hlam, hphi, ht12, p23286_1]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h23274, hlam, p23286_0]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                rcases p23286_3 (m.d 0 1) (by simp) with h23297 | h23297
                                · linarith only [h23297, hlam, p23286_0]
                                · rcases p23286_3 (m.d 1 2) (by simp) with h23299 | h23299
                                  · linarith only [h23243, h23299, hlam]
                                  · linarith only [h0, h23299, hlam]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h0, h23243, hc01, hc23, hlam, hphi, ht12, p23286_1]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [hlam, p23286_0]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h16563, h23243, hc01, hc23, hlam, hphi, ht12, p23286_1]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h17994, h23243, hc01, hc23, hlam, hphi, ht12, p23286_1]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h23243, h23273, hc01, hc23, hlam, hphi, ht12, p23286_1]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h23273, hlam, p23286_1]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h23276, hlam, p23286_0]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [hlam, p23286_0]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h23278, hlam, p23286_1]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                rcases p23286_3 (m.d 0 1) (by simp) with h23311 | h23311
                                · linarith only [h23311, hlam, p23286_0]
                                · rcases p23286_3 (m.d 1 2) (by simp) with h23313 | h23313
                                  · linarith only [h23274, h23313, hlam]
                                  · linarith only [h0, h23313, hlam]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p23286_1]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h23277, hlam, p23286_0]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [h16563, h19110, h22593, h22968, h23243, h23274, h23277, h23280, h23282, hc01, hc23, hc34, hc45, hlam, hphi, ht12, p23286_1]
                              · have p23286_0 := h23286c.1
                                have p23286_1 := h23286c.2.1
                                have p23286_2 := h23286c.2.2.1
                                have p23286_3 := h23286c.2.2.2
                                linarith only [hlam, p23286_0]
                        · linarith only [h23243, h23277, h23281, hlam]
                      · linarith only [h19110, h22593, h22968, h23243, h23277, h23280, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h23322 | h23322
                    · linarith only [h16563, h23241, h23243, h23273, h23322, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h23324 | h23324
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h23325 | h23325
                        · linarith only [h0, h23243, h23277, h23325, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h16563, h23243, h23273, h23325, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h16563, h23243, h23273, h23324, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h14799, h22967, h23276, hlam]
            · linarith only [h0, h22593, h23273, hlam]
    · linarith only [h19110, h22593, h22967, hlam]

end R2N4
