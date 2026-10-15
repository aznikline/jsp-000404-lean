import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_9S22
import Jsp000404.R1LeavesN7_9S24

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13744000 in
set_option maxHeartbeats 13744000 in
theorem r1l7_13_24_L_I_H_I_s9_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h8811 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h8812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  rcases m.htr 0 2 3 (by decide) (by decide) with h9627 | h9627
  · rcases m.htr 0 2 4 (by decide) (by decide) with h9628 | h9628
    · rcases m.htr 0 3 4 (by decide) (by decide) with h9629 | h9629
      · rcases m.htr 0 3 5 (by decide) (by decide) with h9630 | h9630
        · rcases m.htr 0 4 5 (by decide) (by decide) with h9631 | h9631
          · linarith only [h8811, h8812, h9631, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h9633 | h9633
            · rcases m.htr 1 2 4 (by decide) (by decide) with h9634 | h9634
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9635 | h9635
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9636 | h9636
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9637 | h9637
                    · linarith only [h8811, h8812, h9631, h9636, h9637, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9639 | h9639
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9640 | h9640
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h9641 | h9641
                          · linarith only [h8811, h8812, h9628, h9637, h9641, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h9643 | h9643
                            · linarith only [h8811, h8812, h9634, h9637, h9639, h9643, hlam]
                            · rcases h3bigk with h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c | h9645c
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                linarith only [hlam, p9645_0]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                linarith only [h7360, hlam, p9645_1]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                rcases p9645_3 (m.d 0 3) (by simp) with h9648 | h9648
                                · rcases p9645_3 (m.d 1 3) (by simp) with h9649 | h9649
                                  · rcases p9645_3 (m.d 2 3) (by simp) with h9650 | h9650
                                    · linarith only [h9627, h9650, hlam]
                                    · rcases p9645_3 (m.d 3 4) (by simp) with h9652 | h9652
                                      · linarith only [h9629, h9652, hlam]
                                      · rcases p9645_3 (m.d 3 5) (by simp) with h9654 | h9654
                                        · linarith only [h9630, h9654, hlam]
                                        · rcases h4bigk with h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c | h9656c
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [hlam, p9656_0]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [h8811, h8812, h9634, h9639, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9656_1]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [h8811, h8812, h9637, h9639, hc34, hc45, hlam, hphi, p9656_1]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [h8811, h8812, h9637, hc34, hc45, hlam, hphi, p9656_1]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [h9631, hlam, p9656_0]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [h8811, hlam, p9656_1]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [hlam, p9656_0]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [h8811, h8812, h9637, h9639, hc34, hc45, hlam, hphi, p9656_1]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [h8811, h8812, h9637, hc34, hc45, hlam, hphi, p9656_1]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [h9637, hlam, p9656_0]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [h9628, hlam, p9656_1]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [h9634, hlam, p9656_1]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [hlam, p9656_0]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [h0, h9628, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9656_1]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [h9641, hlam, p9656_0]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [h9629, hlam, p9656_1]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [h9635, hlam, p9656_0]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [h9639, hlam, p9656_0]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [hlam, p9656_0]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [h9643, hlam, p9656_0]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [hc04, hc45, hlam, hphi, p9656_1]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [hc14, hc45, hlam, hphi, p9656_1]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [h9639, hc34, hc45, hlam, hphi, p9656_1]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [hc34, hc45, hlam, hphi, p9656_1]
                                          · have p9656_0 := h9656c.1
                                            have p9656_1 := h9656c.2.1
                                            have p9656_2 := h9656c.2.2.1
                                            have p9656_3 := h9656c.2.2.2
                                            linarith only [hlam, p9656_0]
                                  · linarith only [h9633, h9649, hlam]
                                · linarith only [h9627, h9648, hlam]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                rcases p9645_3 (m.d 0 3) (by simp) with h9684 | h9684
                                · rcases p9645_3 (m.d 1 3) (by simp) with h9685 | h9685
                                  · rcases p9645_3 (m.d 2 3) (by simp) with h9686 | h9686
                                    · linarith only [h9627, h9686, hlam]
                                    · linarith only [h9639, h9686, hlam]
                                  · linarith only [h9635, h9685, hlam]
                                · linarith only [h9684, hlam, p9645_0]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                rcases p9645_3 (m.d 0 3) (by simp) with h9691 | h9691
                                · rcases p9645_3 (m.d 1 3) (by simp) with h9692 | h9692
                                  · rcases p9645_3 (m.d 2 3) (by simp) with h9693 | h9693
                                    · linarith only [h9627, h9693, hlam]
                                    · linarith only [h9640, h9693, hlam]
                                  · linarith only [h9636, h9692, hlam]
                                · linarith only [h9691, hlam, p9645_0]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                rcases p9645_3 (m.d 0 3) (by simp) with h9698 | h9698
                                · linarith only [h7360, h9698, hlam]
                                · rcases p9645_3 (m.d 1 3) (by simp) with h9700 | h9700
                                  · rcases p9645_3 (m.d 2 3) (by simp) with h9701 | h9701
                                    · linarith only [h9633, h9701, hlam]
                                    · rcases p9645_3 (m.d 3 4) (by simp) with h9703 | h9703
                                      · linarith only [h9635, h9703, hlam]
                                      · rcases p9645_3 (m.d 3 5) (by simp) with h9705 | h9705
                                        · linarith only [h9636, h9705, hlam]
                                        · rcases h4bigk with h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c | h9707c
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [hlam, p9707_0]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h8811, h8812, h9630, h9633, h9634, h9639, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9645_1, p9707_1]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h8811, h8812, h9630, h9633, h9639, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9645_1, p9707_1]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h8811, h8812, h9630, h9633, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9645_1, p9707_1]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h9631, hlam, p9707_0]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h8811, hlam, p9707_1]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [hlam, p9707_0]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h8811, h8812, h9630, h9633, h9639, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9645_1, p9707_1]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h8811, h8812, h9630, h9633, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9645_1, p9707_1]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h9637, hlam, p9707_0]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h9628, hlam, p9707_1]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h9634, hlam, p9707_1]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [hlam, p9707_0]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h0, h9628, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9707_1]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h9641, hlam, p9707_0]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h9629, hlam, p9707_1]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h9635, hlam, p9707_0]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h9639, hlam, p9707_0]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [hlam, p9707_0]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h9643, hlam, p9707_0]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [hc04, hc45, hlam, hphi, p9707_1]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h9634, hc24, hc45, hlam, hphi, p9707_1]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [h9639, hc34, hc45, hlam, hphi, p9707_1]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [hc34, hc45, hlam, hphi, p9707_1]
                                          · have p9707_0 := h9707c.1
                                            have p9707_1 := h9707c.2.1
                                            have p9707_2 := h9707c.2.2.1
                                            have p9707_3 := h9707c.2.2.2
                                            linarith only [hlam, p9707_0]
                                  · linarith only [h7360, h9700, hlam]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                linarith only [hlam, p9645_0]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                rcases p9645_3 (m.d 0 3) (by simp) with h9735 | h9735
                                · linarith only [h7360, h9735, hlam]
                                · linarith only [h9627, h9735, hlam]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                rcases p9645_3 (m.d 0 3) (by simp) with h9738 | h9738
                                · linarith only [h7360, h9738, hlam]
                                · linarith only [h9629, h9738, hlam]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                rcases p9645_3 (m.d 0 3) (by simp) with h9741 | h9741
                                · linarith only [h7360, h9741, hlam]
                                · linarith only [h9630, h9741, hlam]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                linarith only [h9627, hlam, p9645_0]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                linarith only [h9633, hlam, p9645_0]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                linarith only [hlam, p9645_0]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                rcases p9645_3 (m.d 0 3) (by simp) with h9747 | h9747
                                · rcases p9645_3 (m.d 1 3) (by simp) with h9748 | h9748
                                  · rcases p9645_3 (m.d 2 3) (by simp) with h9749 | h9749
                                    · rcases p9645_3 (m.d 3 4) (by simp) with h9750 | h9750
                                      · linarith only [h9750, hlam, p9645_0]
                                      · rcases p9645_3 (m.d 3 5) (by simp) with h9752 | h9752
                                        · linarith only [h9640, h9752, hlam]
                                        · linarith only [h9643, h9752, hlam]
                                    · linarith only [h9749, hlam, p9645_0]
                                  · linarith only [h9635, h9748, hlam]
                                · linarith only [h9629, h9747, hlam]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                rcases p9645_3 (m.d 0 3) (by simp) with h9758 | h9758
                                · rcases p9645_3 (m.d 1 3) (by simp) with h9759 | h9759
                                  · rcases p9645_3 (m.d 2 3) (by simp) with h9760 | h9760
                                    · rcases p9645_3 (m.d 3 4) (by simp) with h9761 | h9761
                                      · linarith only [h9639, h9761, hlam]
                                      · rcases p9645_3 (m.d 3 5) (by simp) with h9763 | h9763
                                        · linarith only [h9763, hlam, p9645_0]
                                        · rcases h4bigk with h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c | h9765c
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [hlam, p9765_0]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h0, h8811, h9634, h9639, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9765_1]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h8811, h8812, h9637, h9639, hc34, hc45, hlam, hphi, p9765_1]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h8811, h8812, h9637, hc34, hc45, hlam, hphi, p9765_1]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h9631, hlam, p9765_0]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h8811, hlam, p9765_1]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [hlam, p9765_0]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h8811, h8812, h9637, h9639, hc34, hc45, hlam, hphi, p9765_1]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h8811, h8812, h9637, hc34, hc45, hlam, hphi, p9765_1]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h9637, hlam, p9765_0]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h9628, hlam, p9765_1]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h9634, hlam, p9765_1]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [hlam, p9765_0]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h0, h9628, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9765_1]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h9641, hlam, p9765_0]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h9629, hlam, p9765_1]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h9635, hlam, p9765_0]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h9639, hlam, p9765_0]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [hlam, p9765_0]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h9643, hlam, p9765_0]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [hc04, hc45, hlam, hphi, p9765_1]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h9634, hc24, hc45, hlam, hphi, p9765_1]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [h9639, hc34, hc45, hlam, hphi, p9765_1]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [hc34, hc45, hlam, hphi, p9765_1]
                                          · have p9765_0 := h9765c.1
                                            have p9765_1 := h9765c.2.1
                                            have p9765_2 := h9765c.2.2.1
                                            have p9765_3 := h9765c.2.2.2
                                            linarith only [hlam, p9765_0]
                                    · linarith only [h9760, hlam, p9645_0]
                                  · linarith only [h9636, h9759, hlam]
                                · linarith only [h9630, h9758, hlam]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                linarith only [h9629, hlam, p9645_0]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                linarith only [h9635, hlam, p9645_0]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                linarith only [h9639, hlam, p9645_0]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                linarith only [hlam, p9645_0]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                linarith only [h9643, hlam, p9645_1]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                linarith only [h9630, hlam, p9645_0]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                linarith only [h9636, hlam, p9645_0]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                linarith only [h9640, hlam, p9645_0]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                linarith only [h0, h9627, h9640, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9645_1]
                              · have p9645_0 := h9645c.1
                                have p9645_1 := h9645c.2.1
                                have p9645_2 := h9645c.2.2.1
                                have p9645_3 := h9645c.2.2.2
                                linarith only [hlam, p9645_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h9804 | h9804
                          · linarith only [h8811, h8812, h9634, h9637, h9804, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h9806 | h9806
                            · linarith only [h8812, h9630, h9637, h9639, h9640, h9806, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · rcases h3bigk with h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [hlam, p9808_0]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [h7360, hlam, p9808_1]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                rcases p9808_3 (m.d 0 3) (by simp) with h9811 | h9811
                                · rcases p9808_3 (m.d 1 3) (by simp) with h9812 | h9812
                                  · rcases p9808_3 (m.d 2 3) (by simp) with h9813 | h9813
                                    · linarith only [h9627, h9813, hlam]
                                    · rcases p9808_3 (m.d 3 4) (by simp) with h9815 | h9815
                                      · linarith only [h9629, h9815, hlam]
                                      · rcases p9808_3 (m.d 3 5) (by simp) with h9817 | h9817
                                        · linarith only [h9630, h9817, hlam]
                                        · linarith only [h9640, h9817, hlam]
                                  · linarith only [h9633, h9812, hlam]
                                · linarith only [h9627, h9811, hlam]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [h9630, h9639, h9640, hlam, p9808_2]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [h0, h9627, h9639, h9640, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9808_1]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [h9630, h9633, h9639, h9640, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9808_1]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [hlam, p9808_0]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                rcases p9808_3 (m.d 0 3) (by simp) with h9826 | h9826
                                · linarith only [h7360, h9826, hlam]
                                · linarith only [h9627, h9826, hlam]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [h7360, h9630, h9639, h9640, hlam, p9808_2]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [h9639, h9640, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9808_1]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [h9627, hlam, p9808_0]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [h9633, hlam, p9808_0]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [hlam, p9808_0]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [h9630, h9640, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p9808_1]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [h9640, hlam, p9808_0]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [h9629, hlam, p9808_0]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [h9635, hlam, p9808_0]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [h9639, hlam, p9808_0]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [hlam, p9808_0]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [h9806, hlam, p9808_1]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [h9630, hlam, p9808_0]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [h9636, hlam, p9808_0]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [h0, h9627, h9630, h9639, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9808_1]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                rcases p9808_3 (m.d 0 3) (by simp) with h9844 | h9844
                                · rcases p9808_3 (m.d 1 3) (by simp) with h9845 | h9845
                                  · rcases p9808_3 (m.d 2 3) (by simp) with h9846 | h9846
                                    · linarith only [h9640, h9846, hlam]
                                    · linarith only [h9639, h9846, hlam]
                                  · linarith only [h9635, h9845, hlam]
                                · linarith only [h9629, h9844, hlam]
                              · have p9808_0 := h9808c.1
                                have p9808_1 := h9808c.2.1
                                have p9808_2 := h9808c.2.2.1
                                have p9808_3 := h9808c.2.2.2
                                linarith only [hlam, p9808_0]
                      · linarith only [h8811, h8812, h9635, h9637, h9639, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h7360, h9627, h9630, h9636, hc01, hc12, hlam, hphi]
                · linarith only [h7360, h9629, h9635, hlam]
              · linarith only [h0, h9628, h9634, hlam]
            · linarith only [h0, h9627, h9633, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h9857 | h9857
          · linarith only [h7360, h8811, h9630, h9857, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h9859 | h9859
            · rcases m.htr 1 2 4 (by decide) (by decide) with h9860 | h9860
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9861 | h9861
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9862 | h9862
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9863 | h9863
                    · linarith only [h7360, h8811, h9630, h9857, h9859, h9862, h9863, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9865 | h9865
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9866 | h9866
                        · linarith only [h7360, h8811, h9627, h9630, h9866, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h9868 | h9868
                          · linarith only [h7360, h8811, h9630, h9860, h9862, h9863, h9868, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h9870 | h9870
                            · linarith only [h7360, h8811, h9630, h9860, h9862, h9863, h9865, h9870, hlam]
                            · rcases h3bigk with h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h7360, hlam, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9630, h9862, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9630, h9862, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9630, hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                rcases p9872_3 (m.d 0 3) (by simp) with h9878 | h9878
                                · linarith only [h7360, h9878, hlam]
                                · rcases p9872_3 (m.d 1 3) (by simp) with h9880 | h9880
                                  · rcases p9872_3 (m.d 2 3) (by simp) with h9881 | h9881
                                    · linarith only [h9859, h9881, hlam]
                                    · rcases p9872_3 (m.d 3 4) (by simp) with h9883 | h9883
                                      · linarith only [h9861, h9883, hlam]
                                      · rcases p9872_3 (m.d 3 5) (by simp) with h9885 | h9885
                                        · linarith only [h9862, h9885, hlam]
                                        · linarith only [h9630, h9885, hlam]
                                  · linarith only [h7360, h9880, hlam]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                rcases p9872_3 (m.d 0 3) (by simp) with h9890 | h9890
                                · linarith only [h7360, h9890, hlam]
                                · linarith only [h9627, h9890, hlam]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9627, h9630, h9862, h9865, hlam, p9872_2]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h7360, h9630, h9859, hc01, hc12, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9627, hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9859, hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9627, h9630, h9862, h9863, hc34, hc45, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9866, hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9629, hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9861, hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9865, hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9870, hlam, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h7360, h8811, h9860, h9862, h9863, hc24, hc45, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9862, hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9859, h9862, h9865, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                rcases p9872_3 (m.d 0 3) (by simp) with h9908 | h9908
                                · linarith only [h9630, h9908, hlam]
                                · linarith only [h9629, h9908, hlam]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hlam, p9872_0]
                      · linarith only [h9629, h9630, h9859, h9862, h9865, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9913 | h9913
                    · linarith only [h7360, h8811, h9862, h9913, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9915 | h9915
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9916 | h9916
                        · linarith only [h7360, h9862, h9916, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h9918 | h9918
                          · linarith only [h7360, h8811, h9860, h9862, h9913, h9918, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h9920 | h9920
                            · linarith only [h7360, h8811, h9629, h9630, h9862, h9913, h9920, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h7360, h8811, h9860, h9862, h9915, h9920, hc34, hc45, hlam, hphi]
                      · linarith only [h7360, h9629, h9862, h9915, hc23, hc35, hlam, hphi]
                · linarith only [h7360, h8811, h9629, h9861, hlam]
              · linarith only [h7360, h8811, h9628, h9859, h9860, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h9627, h9859, hlam]
      · linarith only [h7360, h8811, h9629, hlam]
    · linarith only [h0, h8811, h9628, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h9929 | h9929
    · rcases m.htr 0 3 4 (by decide) (by decide) with h9930 | h9930
      · rcases m.htr 0 3 5 (by decide) (by decide) with h9931 | h9931
        · rcases m.htr 0 4 5 (by decide) (by decide) with h9932 | h9932
          · linarith only [h8811, h8812, h9932, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h9934 | h9934
            · rcases m.htr 1 2 4 (by decide) (by decide) with h9935 | h9935
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9936 | h9936
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9937 | h9937
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9938 | h9938
                    · linarith only [h0, h8811, h9627, h9932, h9934, h9938, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9940 | h9940
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9941 | h9941
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h9942 | h9942
                          · linarith only [h0, h8811, h9627, h9934, h9935, h9938, h9942, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h9944 | h9944
                            · linarith only [h8811, h8812, h9935, h9938, h9940, h9944, hlam]
                            · rcases h3bigk with h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c | h9946c
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [hlam, p9946_0]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [h7360, hlam, p9946_1]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [h9627, hlam, p9946_1]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                rcases p9946_3 (m.d 0 3) (by simp) with h9950 | h9950
                                · rcases p9946_3 (m.d 1 3) (by simp) with h9951 | h9951
                                  · rcases p9946_3 (m.d 2 3) (by simp) with h9952 | h9952
                                    · rcases p9946_3 (m.d 3 4) (by simp) with h9953 | h9953
                                      · linarith only [h9953, hlam, p9946_0]
                                      · rcases p9946_3 (m.d 3 5) (by simp) with h9955 | h9955
                                        · linarith only [h9931, h9955, hlam]
                                        · linarith only [h9944, h9955, hlam]
                                    · linarith only [h9940, h9952, hlam]
                                  · linarith only [h9936, h9951, hlam]
                                · linarith only [h9950, hlam, p9946_0]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                rcases p9946_3 (m.d 0 3) (by simp) with h9961 | h9961
                                · rcases p9946_3 (m.d 1 3) (by simp) with h9962 | h9962
                                  · rcases p9946_3 (m.d 2 3) (by simp) with h9963 | h9963
                                    · rcases p9946_3 (m.d 3 4) (by simp) with h9964 | h9964
                                      · linarith only [h9930, h9964, hlam]
                                      · rcases p9946_3 (m.d 3 5) (by simp) with h9966 | h9966
                                        · linarith only [h9966, hlam, p9946_0]
                                        · rcases h4bigk with h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [hlam, p9968_0]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [h0, h8811, h9627, h9934, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p9968_1]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [h0, h8811, h9627, h9934, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9968_1]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [h0, h8811, h9627, h9934, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9968_1]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [h9932, hlam, p9968_0]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [h8811, hlam, p9968_1]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [hlam, p9968_0]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [h0, h8811, h9627, h9934, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9968_1]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [h0, h8811, h9627, h9934, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9968_1]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [h9938, hlam, p9968_0]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [h9929, hlam, p9968_1]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [h9935, hlam, p9968_1]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [hlam, p9968_0]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [h9627, h9929, h9934, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9968_1]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [h9942, hlam, p9968_0]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [h9930, hlam, p9968_1]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [h9936, hlam, p9968_0]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [h9940, hlam, p9968_0]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [hlam, p9968_0]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [h9944, hlam, p9968_0]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [hc04, hc45, hlam, hphi, p9968_1]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [hc14, hc45, hlam, hphi, p9968_1]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [h9940, hc34, hc45, hlam, hphi, p9968_1]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [hc34, hc45, hlam, hphi, p9968_1]
                                          · have p9968_0 := h9968c.1
                                            have p9968_1 := h9968c.2.1
                                            have p9968_2 := h9968c.2.2.1
                                            have p9968_3 := h9968c.2.2.2
                                            linarith only [hlam, p9968_0]
                                    · linarith only [h9941, h9963, hlam]
                                  · linarith only [h9937, h9962, hlam]
                                · linarith only [h9961, hlam, p9946_0]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                rcases p9946_3 (m.d 0 3) (by simp) with h9997 | h9997
                                · linarith only [h7360, h9997, hlam]
                                · rcases p9946_3 (m.d 1 3) (by simp) with h9999 | h9999
                                  · rcases p9946_3 (m.d 2 3) (by simp) with h10000 | h10000
                                    · linarith only [h10000, h9934, hlam]
                                    · linarith only [h10000, h9627, hlam]
                                  · linarith only [h7360, h9999, hlam]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [hlam, p9946_0]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [h0, h9627, h9934, hc01, hc12, hlam, hphi, p9946_1]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                rcases p9946_3 (m.d 0 3) (by simp) with h10006 | h10006
                                · linarith only [h10006, h7360, hlam]
                                · linarith only [h10006, h9930, hlam]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                rcases p9946_3 (m.d 0 3) (by simp) with h10009 | h10009
                                · linarith only [h10009, h7360, hlam]
                                · linarith only [h10009, h9931, hlam]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [h0, h8811, h9627, h9934, h9935, h9940, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9946_1]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [h9934, hlam, p9946_0]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [hlam, p9946_0]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                rcases p9946_3 (m.d 0 3) (by simp) with h10015 | h10015
                                · linarith only [h10015, h9627, hlam]
                                · linarith only [h10015, h9930, hlam]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                rcases p9946_3 (m.d 0 3) (by simp) with h10018 | h10018
                                · linarith only [h10018, h9627, hlam]
                                · linarith only [h10018, h9931, hlam]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [h9930, hlam, p9946_0]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [h9936, hlam, p9946_0]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [h9940, hlam, p9946_0]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [hlam, p9946_0]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [h9944, hlam, p9946_1]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [h9931, hlam, p9946_0]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [h9937, hlam, p9946_0]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [h9941, hlam, p9946_0]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [h9627, h9931, h9934, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9946_1]
                              · have p9946_0 := h9946c.1
                                have p9946_1 := h9946c.2.1
                                have p9946_2 := h9946c.2.2.1
                                have p9946_3 := h9946c.2.2.2
                                linarith only [hlam, p9946_0]
                        · linarith only [h9627, h9931, h9941, hlam]
                      · linarith only [h9627, h9930, h9940, hlam]
                  · linarith only [h9627, h9931, h9934, h9937, hlam]
                · linarith only [h9627, h9930, h9934, h9936, hlam]
              · linarith only [h9627, h9929, h9935, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h10036 | h10036
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10037 | h10037
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10038 | h10038
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10039 | h10039
                    · linarith only [h0, h10039, h8811, h9934, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10041 | h10041
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10042 | h10042
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10043 | h10043
                          · linarith only [h0, h10036, h10039, h10043, h8811, h9934, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10045 | h10045
                            · linarith only [h10036, h10039, h10041, h10045, h8811, h8812, hlam]
                            · rcases h3bigk with h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c | h10047c
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                linarith only [hlam, p10047_0]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                linarith only [h7360, hlam, p10047_1]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                linarith only [h9627, hlam, p10047_1]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                rcases p10047_3 (m.d 0 3) (by simp) with h10051 | h10051
                                · rcases p10047_3 (m.d 1 3) (by simp) with h10052 | h10052
                                  · rcases p10047_3 (m.d 2 3) (by simp) with h10053 | h10053
                                    · rcases p10047_3 (m.d 3 4) (by simp) with h10054 | h10054
                                      · linarith only [h10054, hlam, p10047_0]
                                      · rcases p10047_3 (m.d 3 5) (by simp) with h10056 | h10056
                                        · linarith only [h10056, h9931, hlam]
                                        · linarith only [h10045, h10056, hlam]
                                    · linarith only [h10041, h10053, hlam]
                                  · linarith only [h10037, h10052, hlam]
                                · linarith only [h10051, hlam, p10047_0]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                rcases p10047_3 (m.d 0 3) (by simp) with h10062 | h10062
                                · rcases p10047_3 (m.d 1 3) (by simp) with h10063 | h10063
                                  · rcases p10047_3 (m.d 2 3) (by simp) with h10064 | h10064
                                    · rcases p10047_3 (m.d 3 4) (by simp) with h10065 | h10065
                                      · linarith only [h10065, h9930, hlam]
                                      · rcases p10047_3 (m.d 3 5) (by simp) with h10067 | h10067
                                        · linarith only [h10067, hlam, p10047_0]
                                        · rcases h4bigk with h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c | h10069c
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [hlam, p10069_0]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h0, h10036, h10041, h8811, h9934, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10069_1]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h0, h10041, h8811, h9934, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10069_1]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h0, h8811, h9934, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10069_1]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h9932, hlam, p10069_0]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h8811, hlam, p10069_1]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [hlam, p10069_0]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h0, h10041, h8811, h9934, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10069_1]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h0, h8811, h9934, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10069_1]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h10039, hlam, p10069_0]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h9929, hlam, p10069_1]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h10036, hlam, p10069_1]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [hlam, p10069_0]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h0, h9929, h9934, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10069_1]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h10043, hlam, p10069_0]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h9930, hlam, p10069_1]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h10037, hlam, p10069_0]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h10041, hlam, p10069_0]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [hlam, p10069_0]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h10045, hlam, p10069_0]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [hc04, hc45, hlam, hphi, p10069_1]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h10036, hc24, hc45, hlam, hphi, p10069_1]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [h10041, hc34, hc45, hlam, hphi, p10069_1]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [hc34, hc45, hlam, hphi, p10069_1]
                                          · have p10069_0 := h10069c.1
                                            have p10069_1 := h10069c.2.1
                                            have p10069_2 := h10069c.2.2.1
                                            have p10069_3 := h10069c.2.2.2
                                            linarith only [hlam, p10069_0]
                                    · linarith only [h10042, h10064, hlam]
                                  · linarith only [h10038, h10063, hlam]
                                · linarith only [h10062, hlam, p10047_0]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                rcases p10047_3 (m.d 0 3) (by simp) with h10098 | h10098
                                · linarith only [h10098, h7360, hlam]
                                · rcases p10047_3 (m.d 1 3) (by simp) with h10100 | h10100
                                  · rcases p10047_3 (m.d 2 3) (by simp) with h10101 | h10101
                                    · rcases p10047_3 (m.d 3 4) (by simp) with h10102 | h10102
                                      · linarith only [h10037, h10102, hlam]
                                      · rcases p10047_3 (m.d 3 5) (by simp) with h10104 | h10104
                                        · linarith only [h10038, h10104, hlam]
                                        · rcases h4bigk with h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c | h10106c
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [hlam, p10106_0]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [h0, h10036, h10041, h8811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10106_1]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [h0, h10041, h8811, h9627, h9934, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10047_1, p10106_1]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [h0, h8811, h9627, h9934, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10047_1, p10106_1]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [h9932, hlam, p10106_0]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [h8811, hlam, p10106_1]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [hlam, p10106_0]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [h0, h10041, h8811, h9627, h9934, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10047_1, p10106_1]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [h0, h8811, h9627, h9934, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10047_1, p10106_1]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [h10039, hlam, p10106_0]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [h9929, hlam, p10106_1]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [h10036, hlam, p10106_1]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [hlam, p10106_0]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [h9627, h9929, h9934, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10047_1, p10106_1]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [h10043, hlam, p10106_0]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [h9930, hlam, p10106_1]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [h10037, hlam, p10106_0]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [h10041, hlam, p10106_0]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [hlam, p10106_0]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [h10045, hlam, p10106_0]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [hc04, hc45, hlam, hphi, p10106_1]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [hc14, hc45, hlam, hphi, p10106_1]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [h10041, hc34, hc45, hlam, hphi, p10106_1]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [hc34, hc45, hlam, hphi, p10106_1]
                                          · have p10106_0 := h10106c.1
                                            have p10106_1 := h10106c.2.1
                                            have p10106_2 := h10106c.2.2.1
                                            have p10106_3 := h10106c.2.2.2
                                            linarith only [hlam, p10106_0]
                                    · linarith only [h10101, h9627, hlam]
                                  · linarith only [h10100, h7360, hlam]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                linarith only [hlam, p10047_0]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                linarith only [h9934, hlam, p10047_1]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                rcases p10047_3 (m.d 0 3) (by simp) with h10136 | h10136
                                · linarith only [h10136, h7360, hlam]
                                · linarith only [h10136, h9930, hlam]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                rcases p10047_3 (m.d 0 3) (by simp) with h10139 | h10139
                                · linarith only [h10139, h7360, hlam]
                                · linarith only [h10139, h9931, hlam]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                rcases p10047_3 (m.d 0 3) (by simp) with h10142 | h10142
                                · linarith only [h10142, h9627, hlam]
                                · rcases p10047_3 (m.d 1 3) (by simp) with h10144 | h10144
                                  · linarith only [h10144, h9934, hlam]
                                  · linarith only [h10144, h7360, hlam]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                linarith only [h10036, h10041, h7360, h8811, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10047_1]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                linarith only [hlam, p10047_0]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                linarith only [h0, h10036, h10041, h8811, h9934, hlam, p10047_2]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                rcases p10047_3 (m.d 0 3) (by simp) with h10150 | h10150
                                · linarith only [h10150, h9627, hlam]
                                · linarith only [h10150, h9931, hlam]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                linarith only [h9930, hlam, p10047_0]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                linarith only [h10037, hlam, p10047_0]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                linarith only [h10041, hlam, p10047_0]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                linarith only [hlam, p10047_0]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                linarith only [h10045, hlam, p10047_1]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                linarith only [h9931, hlam, p10047_0]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                linarith only [h10038, hlam, p10047_0]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                linarith only [h10042, hlam, p10047_0]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                rcases p10047_3 (m.d 0 3) (by simp) with h10161 | h10161
                                · rcases p10047_3 (m.d 1 3) (by simp) with h10162 | h10162
                                  · rcases p10047_3 (m.d 2 3) (by simp) with h10163 | h10163
                                    · rcases p10047_3 (m.d 3 4) (by simp) with h10164 | h10164
                                      · linarith only [h10045, h10164, hlam]
                                      · rcases p10047_3 (m.d 3 5) (by simp) with h10166 | h10166
                                        · rcases h4bigk with h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c | h10167c
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [hlam, p10167_0]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h0, h10036, h10041, h8811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10167_1]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h0, h10041, h8811, h9934, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10167_1]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h0, h8811, h9934, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10167_1]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h9932, hlam, p10167_0]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h8811, hlam, p10167_1]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [hlam, p10167_0]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h0, h10041, h8811, h9934, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10167_1]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h0, h8811, h9934, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10167_1]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h10039, hlam, p10167_0]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h9929, hlam, p10167_1]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h10036, hlam, p10167_1]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [hlam, p10167_0]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h9929, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p10167_1]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h10043, hlam, p10167_0]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h9930, hlam, p10167_1]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h10037, hlam, p10167_0]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h10041, hlam, p10167_0]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [hlam, p10167_0]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h10045, hlam, p10167_0]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [hc04, hc45, hlam, hphi, p10167_1]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h10036, hc24, hc45, hlam, hphi, p10167_1]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [h10041, hc34, hc45, hlam, hphi, p10167_1]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [hc34, hc45, hlam, hphi, p10167_1]
                                          · have p10167_0 := h10167c.1
                                            have p10167_1 := h10167c.2.1
                                            have p10167_2 := h10167c.2.2.1
                                            have p10167_3 := h10167c.2.2.2
                                            linarith only [hlam, p10167_0]
                                        · linarith only [h10045, h10166, hlam]
                                    · linarith only [h10041, h10163, hlam]
                                  · linarith only [h10037, h10162, hlam]
                                · linarith only [h10161, h9930, hlam]
                              · have p10047_0 := h10047c.1
                                have p10047_1 := h10047c.2.1
                                have p10047_2 := h10047c.2.2.1
                                have p10047_3 := h10047c.2.2.2
                                linarith only [hlam, p10047_0]
                        · linarith only [h0, h10042, h9931, h9934, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · linarith only [h10041, h7360, h9930, h9934, hlam]
                  · linarith only [h10038, h7360, h9931, hlam]
                · linarith only [h10037, h7360, h9930, hlam]
              · linarith only [h0, h10036, h8811, h9929, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h10203 | h10203
          · linarith only [h0, h10203, h8811, h9627, h9931, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h10205 | h10205
            · rcases m.htr 1 2 4 (by decide) (by decide) with h10206 | h10206
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10207 | h10207
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10208 | h10208
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10209 | h10209
                    · linarith only [h0, h10203, h10205, h10208, h10209, h8811, h9627, h9931, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10211 | h10211
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10212 | h10212
                        · linarith only [h0, h10205, h10212, h9627, h9931, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h10206, h10208, h10209, h10211, h10212, h8811, h9627, hc34, hc45, hlam, hphi]
                      · linarith only [h0, h10211, h8811, h9627, h9930, h9931, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10216 | h10216
                    · linarith only [h10203, h10208, h10216, h7360, h8811, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10218 | h10218
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10219 | h10219
                        · linarith only [h10205, h10208, h10219, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10221 | h10221
                          · linarith only [h0, h10205, h10206, h10208, h10216, h10221, h8811, h9627, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10223 | h10223
                            · linarith only [h0, h10205, h10206, h10208, h10216, h10218, h10223, h8811, h9627, hlam]
                            · linarith only [h0, h10205, h10206, h10208, h10218, h10223, h8811, h9627, hc34, hc45, hlam, hphi]
                      · linarith only [h0, h10206, h10218, h8811, h9627, h9930, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h10205, h10207, h8811, h9627, h9930, hlam]
              · linarith only [h10206, h9627, h9929, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h10229 | h10229
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10230 | h10230
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10231 | h10231
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10232 | h10232
                    · linarith only [h0, h10205, h10231, h10232, h8811, h9627, h9931, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10234 | h10234
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10235 | h10235
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10236 | h10236
                          · linarith only [h0, h10205, h10229, h10231, h10232, h10236, h8811, h9627, h9931, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10238 | h10238
                            · linarith only [h0, h10229, h10231, h10232, h10234, h10238, h8811, h9627, h9931, hlam]
                            · rcases h3bigk with h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c | h10240c
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [hlam, p10240_0]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [h7360, hlam, p10240_1]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [h9627, hlam, p10240_1]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [h10205, h10231, h9931, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10240_1]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [h9931, hlam, p10240_0]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                rcases p10240_3 (m.d 0 3) (by simp) with h10246 | h10246
                                · linarith only [h10246, h7360, hlam]
                                · rcases p10240_3 (m.d 1 3) (by simp) with h10248 | h10248
                                  · rcases p10240_3 (m.d 2 3) (by simp) with h10249 | h10249
                                    · rcases p10240_3 (m.d 3 4) (by simp) with h10250 | h10250
                                      · linarith only [h10230, h10250, hlam]
                                      · rcases p10240_3 (m.d 3 5) (by simp) with h10252 | h10252
                                        · linarith only [h10231, h10252, hlam]
                                        · linarith only [h10252, h9931, hlam]
                                    · linarith only [h10249, h9627, hlam]
                                  · linarith only [h10248, h7360, hlam]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [hlam, p10240_0]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [h10205, hlam, p10240_1]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [h10231, h9930, h9931, hlam, p10240_2]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [h0, h10205, h9627, h9931, hc01, hc23, hlam, hphi, ht12, p10240_1]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                rcases p10240_3 (m.d 0 3) (by simp) with h10261 | h10261
                                · linarith only [h10261, h9627, hlam]
                                · rcases p10240_3 (m.d 1 3) (by simp) with h10263 | h10263
                                  · linarith only [h10205, h10263, hlam]
                                  · linarith only [h10263, h7360, hlam]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [h10229, h10234, h7360, h8811, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10240_1]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [hlam, p10240_0]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [h0, h10205, h10229, h10234, h8811, hlam, p10240_2]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [h0, h10229, h10234, h8811, h9627, h9931, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10240_1]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [h9930, hlam, p10240_0]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [h10230, hlam, p10240_0]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [h10234, hlam, p10240_0]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [hlam, p10240_0]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [h10238, hlam, p10240_1]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [h0, h10229, h10231, h10234, h8811, h9627, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10240_1]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [h10231, hlam, p10240_0]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [h10235, hlam, p10240_0]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                rcases p10240_3 (m.d 0 3) (by simp) with h10278 | h10278
                                · linarith only [h10278, h9931, hlam]
                                · linarith only [h10278, h9930, hlam]
                              · have p10240_0 := h10240c.1
                                have p10240_1 := h10240c.2.1
                                have p10240_2 := h10240c.2.2.1
                                have p10240_3 := h10240c.2.2.2
                                linarith only [hlam, p10240_0]
                        · linarith only [h10205, h10231, h10235, hlam]
                      · linarith only [h10205, h10234, h7360, h9930, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10284 | h10284
                    · linarith only [h0, h10203, h10205, h10284, h8811, h9627, h9931, hc02, hc23, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10286 | h10286
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10287 | h10287
                        · linarith only [h0, h10205, h10229, h10231, h10286, h10287, h8811, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h10205, h10229, h10286, h10287, h8811, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h10205, h10229, h10286, h8811, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h10205, h10229, h10230, h8811, h9930, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h10229, h9929, hlam]
      · linarith only [h7360, h8811, h9930, hlam]
    · linarith only [h0, h8811, h9929, hlam]

set_option maxHeartbeats 13744000 in
set_option maxHeartbeats 13744000 in
theorem r1l7_13_24_L_I_H_I_s9_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h8811 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  rcases m.htr 0 1 5 (by decide) (by decide) with h8812 | h8812
  · exact r1l7_13_24_L_I_H_I_s9_x0_x0 m hb3 hb4 hg0 hg7360 h8811 h8812
  · exact r1l7_13_24_L_I_H_I_s9_x0_x1 m hb3 hb4 hg0 hg7360 h8811 h8812

set_option maxHeartbeats 13744000 in
set_option maxHeartbeats 13744000 in
theorem r1l7_13_24_L_I_H_I_s9_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  exact r1l7_13_24_L_I_H_I_s10 m hb3 hb4 h0 h7360 h8811

set_option maxHeartbeats 13744000 in
set_option maxHeartbeats 13744000 in
theorem r1l7_13_24_L_I_H_I_s9 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  rcases m.htr 0 1 4 (by decide) (by decide) with h8811 | h8811
  · exact r1l7_13_24_L_I_H_I_s9_x0 m hb3 hb4 hg0 hg7360 h8811
  · exact r1l7_13_24_L_I_H_I_s9_x1 m hb3 hb4 hg0 hg7360 h8811

end R2N4
