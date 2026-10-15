import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h4611 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4612 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4613 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4614 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4615 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4616 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h4617 | h4617
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4618 | h4618
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4619 | h4619
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4620 | h4620
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4621 | h4621
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4622 | h4622
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4623 | h4623
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4624 | h4624
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4625 | h4625
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4626 | h4626
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4627 | h4627
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4628 | h4628
                        · linarith only [h4610, h4619, h4625, h4628, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h0, h4610, h4622, h4624, h4628, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h0, h4610, h4622, h4624, h4627, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h0, h4610, h4623, h4626, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h4610, h4622, h4625, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4634 | h4634
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4635 | h4635
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4636 | h4636
                      · linarith only [h4614, h4624, h4636, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4638 | h4638
                        · linarith only [h4620, h4624, h4634, h4638, hlam]
                        · rcases h0bigk with h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c | h4640c
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [hlam, p4640_0]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h0, hlam, p4640_1]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h0, h4613, h4635, h4638, hc34, hlam, hphi, ht0b, ht45, ht5b, p4640_1, u0elo1]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h0, h4618, h4620, h4624, h4634, hc34, hlam, hphi, ht0b, ht45, ht5b, p4640_1, u0elo1]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h0, h4618, h4620, h4624, h4634, hc34, hlam, hphi, ht0b, ht45, ht5b, p4640_1, u0elo1]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h4610, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4640_1, u0elo1]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [hlam, p4640_0]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h4616, h4618, h4620, h4624, h4634, hc34, hlam, hphi, ht0b, ht45, ht5b, p4640_1, u0elo1]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h4618, h4620, h4624, h4634, hc34, hlam, hphi, ht0b, ht45, ht5b, p4640_1, u0elo1]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h4618, h4620, h4624, h4634, hc34, hlam, hphi, ht0b, ht45, ht5b, p4640_1, u0elo1]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h4610, hlam, p4640_1]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h4613, hlam, p4640_1]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [hlam, p4640_0]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h4610, h4618, h4620, h4624, h4634, hc34, hlam, hphi, ht0b, ht45, ht5b, p4640_1, u0elo0]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h0, h4610, h4618, h4620, h4624, h4634, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4640_1]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h4611, hlam, p4640_0]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h4614, hlam, p4640_0]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h4616, hlam, p4640_0]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [hlam, p4640_0]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h4618, h4620, h4624, h4634, hc34, hlam, hphi, ht0b, ht45, ht5b, p4640_1, u0elo3]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h4612, hlam, p4640_0]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h4615, hlam, p4640_1]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h4617, hlam, p4640_0]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [h4618, hlam, p4640_1]
                          · have p4640_0 := h4640c.1
                            have p4640_1 := h4640c.2.1
                            have p4640_2 := h4640c.2.2.1
                            have p4640_3 := h4640c.2.2.2
                            linarith only [hlam, p4640_0]
                    · linarith only [h0, h4610, h4623, h4635, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h4610, h4622, h4634, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h4610, h4617, h4622, h4623, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4669 | h4669
              · linarith only [h0, h4610, h4616, h4622, h4669, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4671 | h4671
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4672 | h4672
                  · linarith only [h4613, h4622, h4672, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4674 | h4674
                    · linarith only [h4619, h4669, h4674, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4676 | h4676
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4677 | h4677
                        · rcases h0bigk with h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c | h4678c
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [hlam, p4678_0]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h0, hlam, p4678_1]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h0, h4611, h4616, h4620, h4676, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4678_1]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h0, h4611, h4620, h4676, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4678_1]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h0, h4617, h4619, h4669, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4678_1]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h4610, h4619, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4678_1, u0elo1]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [hlam, p4678_0]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h4616, h4619, h4669, h4677, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4678_1, u0elo1]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h4616, h4619, h4669, h4677, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4678_1, u0elo1]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h4617, h4619, h4669, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4678_1, u0elo1]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h4610, hlam, p4678_1]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h4613, hlam, p4678_1]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [hlam, p4678_0]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h4610, h4616, h4619, h4669, h4677, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4678_1, u0elo0]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h0, h4610, h4617, h4619, h4669, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4678_1]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h4611, hlam, p4678_0]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h4614, hlam, p4678_0]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h4616, hlam, p4678_0]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [hlam, p4678_0]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h4617, h4619, h4669, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4678_1, u0elo3]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h4612, hlam, p4678_0]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h4615, hlam, p4678_1]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h4617, hlam, p4678_0]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [h4618, hlam, p4678_1]
                          · have p4678_0 := h4678c.1
                            have p4678_1 := h4678c.2.1
                            have p4678_2 := h4678c.2.2.1
                            have p4678_3 := h4678c.2.2.2
                            linarith only [hlam, p4678_0]
                        · linarith only [h0, h4611, h4620, h4676, h4677, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h4610, h4616, h4622, h4671, h4676, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4706 | h4706
                  · linarith only [h0, h4610, h4617, h4619, h4669, h4706, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4708 | h4708
                    · linarith only [h0, h4610, h4616, h4618, h4619, h4622, h4671, h4708, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4710 | h4710
                      · linarith only [h4614, h4619, h4622, h4671, h4710, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4712 | h4712
                        · linarith only [h0, h4610, h4616, h4619, h4622, h4671, h4712, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h4618, h4619, h4622, h4712, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
          · linarith only [h0, h4615, h4621, hlam]
        · linarith only [h0, h4614, h4620, hlam]
      · linarith only [h0, h4613, h4619, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4718 | h4718
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4719 | h4719
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4720 | h4720
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4721 | h4721
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4722 | h4722
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4723 | h4723
                · linarith only [h4611, h4618, h4723, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4725 | h4725
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4726 | h4726
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4727 | h4727
                      · linarith only [h4612, h4618, h4719, h4723, h4727, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4729 | h4729
                        · linarith only [h0, h4610, h4611, h4618, h4718, h4725, h4729, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h0bigk with h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c | h4731c
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [hlam, p4731_0]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [h0, hlam, p4731_1]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [h0, h4616, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4731_1]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            rcases p4731_3 (m.d 0 1) (by simp) with h4735 | h4735
                            · rcases p4731_3 (m.d 0 2) (by simp) with h4736 | h4736
                              · rcases p4731_3 (m.d 0 3) (by simp) with h4737 | h4737
                                · linarith only [h4610, h4737, hlam]
                                · linarith only [h4616, h4737, hlam]
                              · linarith only [h4614, h4736, hlam]
                            · linarith only [h4611, h4735, hlam]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            rcases p4731_3 (m.d 0 1) (by simp) with h4742 | h4742
                            · rcases p4731_3 (m.d 0 2) (by simp) with h4743 | h4743
                              · rcases p4731_3 (m.d 0 3) (by simp) with h4744 | h4744
                                · linarith only [h4610, h4744, hlam]
                                · linarith only [h4617, h4744, hlam]
                              · linarith only [h4615, h4743, hlam]
                            · linarith only [h4612, h4742, hlam]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [h4610, h4718, h4726, h4729, hc34, hlam, hphi, ht0b, ht45, ht5b, p4731_1, u0elo1]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [hlam, p4731_0]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [h4610, h4718, h4726, h4729, hc34, hlam, hphi, ht0b, ht45, ht5b, p4731_1, u0elo1]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            rcases p4731_3 (m.d 0 1) (by simp) with h4752 | h4752
                            · linarith only [h0, h4752, hlam]
                            · linarith only [h4611, h4752, hlam]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            rcases p4731_3 (m.d 0 1) (by simp) with h4755 | h4755
                            · linarith only [h0, h4755, hlam]
                            · linarith only [h4612, h4755, hlam]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [h4610, hlam, p4731_1]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [h4613, hlam, p4731_1]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [hlam, p4731_0]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            rcases p4731_3 (m.d 0 1) (by simp) with h4761 | h4761
                            · rcases p4731_3 (m.d 0 2) (by simp) with h4762 | h4762
                              · rcases p4731_3 (m.d 0 3) (by simp) with h4763 | h4763
                                · rcases p4731_3 (m.d 0 4) (by simp) with h4764 | h4764
                                  · linarith only [h4616, h4764, hlam]
                                  · rcases p4731_3 (m.d 0 5) (by simp) with h4766 | h4766
                                    · linarith only [h4617, h4766, hlam]
                                    · linarith only [h4618, h4766, hlam]
                                · linarith only [h4616, h4763, hlam]
                              · linarith only [h4614, h4762, hlam]
                            · linarith only [h4611, h4761, hlam]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            rcases p4731_3 (m.d 0 1) (by simp) with h4772 | h4772
                            · rcases p4731_3 (m.d 0 2) (by simp) with h4773 | h4773
                              · rcases p4731_3 (m.d 0 3) (by simp) with h4774 | h4774
                                · rcases p4731_3 (m.d 0 4) (by simp) with h4775 | h4775
                                  · linarith only [h4616, h4775, hlam]
                                  · rcases p4731_3 (m.d 0 5) (by simp) with h4777 | h4777
                                    · linarith only [h4617, h4777, hlam]
                                    · rcases h2bigk with h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [hlam, p4779_0]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [h0, hlam, p4779_1]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [h4726, h4729, hc34, hlam, hphi, ht0b, ht45, ht5b, p4779_1, u0elo1]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        rcases p4779_3 (m.d 0 2) (by simp) with h4783 | h4783
                                        · rcases p4779_3 (m.d 1 2) (by simp) with h4784 | h4784
                                          · rcases p4779_3 (m.d 2 3) (by simp) with h4785 | h4785
                                            · linarith only [h4613, h4785, hlam]
                                            · linarith only [h4725, h4785, hlam]
                                          · linarith only [h4719, h4784, hlam]
                                        · linarith only [h4783, hlam, p4779_0]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        rcases p4779_3 (m.d 0 2) (by simp) with h4790 | h4790
                                        · rcases p4779_3 (m.d 1 2) (by simp) with h4791 | h4791
                                          · rcases p4779_3 (m.d 2 3) (by simp) with h4792 | h4792
                                            · linarith only [h4613, h4792, hlam]
                                            · linarith only [h4726, h4792, hlam]
                                          · linarith only [h4720, h4791, hlam]
                                        · linarith only [h4790, hlam, p4779_0]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [h0, h4610, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p4731_1, p4779_1]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [hlam, p4779_0]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        rcases p4779_3 (m.d 0 2) (by simp) with h4799 | h4799
                                        · linarith only [h0, h4799, hlam]
                                        · linarith only [h4613, h4799, hlam]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [h0, h4610, h4611, h4618, h4719, hlam, p4731_1, p4779_2]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [h0, h4610, h4615, hlam, p4731_1, p4779_2]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [h4613, hlam, p4779_0]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [h4718, hlam, p4779_0]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [hlam, p4779_0]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [h4610, h4718, h4725, hc34, hlam, hphi, ht0b, ht45, ht5b, p4779_1, u0elo0]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [h0, h4610, h4718, hc25, hlam, hphi, ht0b, ht5b, p4779_1, u0elo1]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [h4614, hlam, p4779_0]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [h4719, hlam, p4779_0]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [h4725, hlam, p4779_1]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [hlam, p4779_0]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [h4727, hlam, p4779_1]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [h4615, hlam, p4779_0]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [h4720, hlam, p4779_0]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [h4726, hlam, p4779_1]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [h4615, h4725, hc34, hlam, hphi, ht0b, ht45, ht5b, p4779_1, u0elo1]
                                      · have p4779_0 := h4779c.1
                                        have p4779_1 := h4779c.2.1
                                        have p4779_2 := h4779c.2.2.1
                                        have p4779_3 := h4779c.2.2.2
                                        linarith only [hlam, p4779_0]
                                · linarith only [h4617, h4774, hlam]
                              · linarith only [h4615, h4773, hlam]
                            · linarith only [h4612, h4772, hlam]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [h4611, hlam, p4731_0]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [h4614, hlam, p4731_0]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [h4616, hlam, p4731_0]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [hlam, p4731_0]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [h4618, hlam, p4731_0]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [h4612, hlam, p4731_0]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [h4615, hlam, p4731_1]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [h4617, hlam, p4731_0]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            rcases p4731_3 (m.d 0 1) (by simp) with h4830 | h4830
                            · rcases p4731_3 (m.d 0 2) (by simp) with h4831 | h4831
                              · rcases p4731_3 (m.d 0 3) (by simp) with h4832 | h4832
                                · rcases p4731_3 (m.d 0 4) (by simp) with h4833 | h4833
                                  · linarith only [h4618, h4833, hlam]
                                  · rcases p4731_3 (m.d 0 5) (by simp) with h4835 | h4835
                                    · rcases h2bigk with h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c | h4836c
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [hlam, p4836_0]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [h0, hlam, p4836_1]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [h4725, hc34, hlam, hphi, ht0b, ht45, ht5b, p4836_1, u0elo1]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        rcases p4836_3 (m.d 0 2) (by simp) with h4840 | h4840
                                        · rcases p4836_3 (m.d 1 2) (by simp) with h4841 | h4841
                                          · rcases p4836_3 (m.d 2 3) (by simp) with h4842 | h4842
                                            · linarith only [h4613, h4842, hlam]
                                            · linarith only [h4725, h4842, hlam]
                                          · linarith only [h4719, h4841, hlam]
                                        · linarith only [h4840, hlam, p4836_0]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        rcases p4836_3 (m.d 0 2) (by simp) with h4847 | h4847
                                        · rcases p4836_3 (m.d 1 2) (by simp) with h4848 | h4848
                                          · rcases p4836_3 (m.d 2 3) (by simp) with h4849 | h4849
                                            · linarith only [h4613, h4849, hlam]
                                            · linarith only [h4726, h4849, hlam]
                                          · linarith only [h4720, h4848, hlam]
                                        · linarith only [h4847, hlam, p4836_0]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [h0, h4611, h4612, h4719, h4725, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4731_1, p4836_1]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [hlam, p4836_0]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        rcases p4836_3 (m.d 0 2) (by simp) with h4856 | h4856
                                        · linarith only [h0, h4856, hlam]
                                        · linarith only [h4613, h4856, hlam]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [h0, h4610, h4611, h4617, h4719, hlam, p4731_1, p4836_2]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        rcases p4836_3 (m.d 0 2) (by simp) with h4860 | h4860
                                        · linarith only [h0, h4860, hlam]
                                        · linarith only [h4615, h4860, hlam]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [h4613, hlam, p4836_0]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [h4718, hlam, p4836_0]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [hlam, p4836_0]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [h4613, h4725, hc34, hlam, hphi, ht0b, ht45, ht5b, p4836_1, u0elo1]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [h4610, h4718, hc25, hlam, hphi, ht0b, ht5b, p4836_1, u0elo0]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [h4614, hlam, p4836_0]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [h4719, hlam, p4836_0]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [h4725, hlam, p4836_1]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [hlam, p4836_0]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [h4727, hlam, p4836_1]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [h4615, hlam, p4836_0]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [h4720, hlam, p4836_0]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [h4726, hlam, p4836_1]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [h4615, h4725, hc34, hlam, hphi, ht0b, ht45, ht5b, p4836_1, u0elo1]
                                      · have p4836_0 := h4836c.1
                                        have p4836_1 := h4836c.2.1
                                        have p4836_2 := h4836c.2.2.1
                                        have p4836_3 := h4836c.2.2.2
                                        linarith only [hlam, p4836_0]
                                    · linarith only [h4618, h4835, hlam]
                                · linarith only [h4616, h4832, hlam]
                              · linarith only [h4614, h4831, hlam]
                            · linarith only [h4611, h4830, hlam]
                          · have p4731_0 := h4731c.1
                            have p4731_1 := h4731c.2.1
                            have p4731_2 := h4731c.2.2.1
                            have p4731_3 := h4731c.2.2.2
                            linarith only [hlam, p4731_0]
                    · linarith only [h0, h4610, h4722, h4726, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h4610, h4721, h4725, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h4610, h4617, h4721, h4722, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4886 | h4886
              · linarith only [h0, h4610, h4616, h4721, h4886, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4888 | h4888
                · linarith only [h0, h4611, h4618, h4888, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4890 | h4890
                  · linarith only [h4718, h4721, h4890, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4892 | h4892
                    · linarith only [h4610, h4616, h4718, h4721, h4886, h4888, h4892, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4894 | h4894
                      · linarith only [h4614, h4618, h4894, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4896 | h4896
                        · linarith only [h0, h4610, h4616, h4617, h4618, h4718, h4886, h4896, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases h0bigk with h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [hlam, p4898_0]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h0, hlam, p4898_1]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h0, h4616, h4718, h4721, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4898_1]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h0, h4616, h4718, h4721, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4898_1]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h0, h4616, h4618, h4718, h4721, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4898_1]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h4610, h4718, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4898_1, u0elo1]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [hlam, p4898_0]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h4616, h4718, h4721, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4898_1, u0elo1]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h4616, h4718, h4721, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4898_1, u0elo1]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h4616, h4618, h4718, h4721, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4898_1, u0elo1]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h4610, hlam, p4898_1]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h4613, hlam, p4898_1]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [hlam, p4898_0]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h4610, h4616, h4718, h4721, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4898_1, u0elo0]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h0, h4610, h4616, h4618, h4718, h4721, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4898_1]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h4611, hlam, p4898_0]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h4614, hlam, p4898_0]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h4616, hlam, p4898_0]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [hlam, p4898_0]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h4618, hlam, p4898_0]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h4612, hlam, p4898_0]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h4615, hlam, p4898_1]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h4617, hlam, p4898_0]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [h4616, h4718, h4721, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4898_1, u0elo4]
                          · have p4898_0 := h4898c.1
                            have p4898_1 := h4898c.2.1
                            have p4898_2 := h4898c.2.2.1
                            have p4898_3 := h4898c.2.2.2
                            linarith only [hlam, p4898_0]
          · linarith only [h0, h4615, h4720, hlam]
        · linarith only [h0, h4614, h4719, hlam]
      · linarith only [h0, h4613, h4718, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4927 | h4927
    · linarith only [h4616, h4617, h4927, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4929 | h4929
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4930 | h4930
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4931 | h4931
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4932 | h4932
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4933 | h4933
              · linarith only [h4610, h4617, h4933, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4935 | h4935
                · linarith only [h0, h4611, h4927, h4935, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4937 | h4937
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4938 | h4938
                    · linarith only [h4610, h4617, h4929, h4938, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4940 | h4940
                      · linarith only [h0, h4610, h4611, h4617, h4927, h4929, h4930, h4937, h4940, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4942 | h4942
                        · linarith only [h4610, h4927, h4929, h4937, h4942, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · rcases h0bigk with h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c | h4944c
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [hlam, p4944_0]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [h0, hlam, p4944_1]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [h0, h4616, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4944_1]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            rcases p4944_3 (m.d 0 1) (by simp) with h4948 | h4948
                            · rcases p4944_3 (m.d 0 2) (by simp) with h4949 | h4949
                              · rcases p4944_3 (m.d 0 3) (by simp) with h4950 | h4950
                                · linarith only [h4610, h4950, hlam]
                                · linarith only [h4616, h4950, hlam]
                              · linarith only [h4614, h4949, hlam]
                            · linarith only [h4611, h4948, hlam]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [h0, h4610, h4617, h4929, h4937, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4944_1]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [h4610, h4929, h4937, hc34, hlam, hphi, ht0b, ht45, ht5b, p4944_1, u0elo1]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [hlam, p4944_0]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [h4610, h4929, h4937, hc34, hlam, hphi, ht0b, ht45, ht5b, p4944_1, u0elo1]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            rcases p4944_3 (m.d 0 1) (by simp) with h4959 | h4959
                            · linarith only [h0, h4959, hlam]
                            · linarith only [h4611, h4959, hlam]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [h4610, h4617, h4929, h4937, hc34, hlam, hphi, ht0b, ht45, ht5b, p4944_1, u0elo1]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [h4610, hlam, p4944_1]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [h4613, hlam, p4944_1]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [hlam, p4944_0]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [h4611, h4617, h4930, h4937, h4942, hc34, hc45, hlam, hphi, p4944_1]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [h4617, hlam, p4944_1]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [h4611, hlam, p4944_0]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [h4614, hlam, p4944_0]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [h4616, hlam, p4944_0]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [hlam, p4944_0]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [h4927, hlam, p4944_0]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [h4612, hlam, p4944_0]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [h4615, hlam, p4944_1]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [h4610, h4929, h4937, hc34, hlam, hphi, ht0b, ht45, ht5b, p4944_1, u0elo4]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            rcases p4944_3 (m.d 0 1) (by simp) with h4976 | h4976
                            · rcases p4944_3 (m.d 0 2) (by simp) with h4977 | h4977
                              · rcases p4944_3 (m.d 0 3) (by simp) with h4978 | h4978
                                · linarith only [h4617, h4978, hlam]
                                · linarith only [h4616, h4978, hlam]
                              · linarith only [h4614, h4977, hlam]
                            · linarith only [h4611, h4976, hlam]
                          · have p4944_0 := h4944c.1
                            have p4944_1 := h4944c.2.1
                            have p4944_2 := h4944c.2.2.1
                            have p4944_3 := h4944c.2.2.2
                            linarith only [hlam, p4944_0]
                  · linarith only [h4616, h4617, h4937, hc23, hc35, hlam, hphi]
            · linarith only [h4616, h4617, h4932, hc13, hc35, hlam, hphi]
          · linarith only [h0, h4615, h4931, hlam]
        · linarith only [h0, h4614, h4930, hlam]
      · linarith only [h0, h4613, h4929, hlam]

set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h4611 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4612 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4613 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4614 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4615 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4616 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4989 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h4990 | h4990
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4991 | h4991
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4992 | h4992
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4993 | h4993
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4994 | h4994
          · linarith only [h4610, h4616, h4994, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4996 | h4996
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4997 | h4997
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4998 | h4998
                · linarith only [h4611, h4616, h4991, h4994, h4998, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5000 | h5000
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5001 | h5001
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5002 | h5002
                      · rcases h0bigk with h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c | h5003c
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [hlam, p5003_0]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [h0, hlam, p5003_1]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [h0, h4613, h5000, h5002, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5003_1]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [h0, h4614, h4998, h5000, h5002, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5003_1]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          rcases p5003_3 (m.d 0 1) (by simp) with h5008 | h5008
                          · rcases p5003_3 (m.d 0 2) (by simp) with h5009 | h5009
                            · rcases p5003_3 (m.d 0 3) (by simp) with h5010 | h5010
                              · linarith only [h4610, h5010, hlam]
                              · linarith only [h4989, h5010, hlam]
                            · linarith only [h4615, h5009, hlam]
                          · linarith only [h4612, h5008, hlam]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [h4610, h4991, h5000, h5002, hc45, hlam, hphi, ht0b, ht5b, p5003_1, u0elo1]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [hlam, p5003_0]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [h4610, h4991, h5000, h5002, hc45, hlam, hphi, ht0b, ht5b, p5003_1, u0elo1]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [h4610, h4616, h4991, h5000, h5002, hc45, hlam, hphi, ht0b, ht5b, p5003_1, u0elo1]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          rcases p5003_3 (m.d 0 1) (by simp) with h5019 | h5019
                          · linarith only [h0, h5019, hlam]
                          · linarith only [h4612, h5019, hlam]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [h4610, hlam, p5003_1]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [h4613, hlam, p5003_1]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [hlam, p5003_0]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [h4616, hlam, p5003_1]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          rcases p5003_3 (m.d 0 1) (by simp) with h5026 | h5026
                          · rcases p5003_3 (m.d 0 2) (by simp) with h5027 | h5027
                            · rcases p5003_3 (m.d 0 3) (by simp) with h5028 | h5028
                              · rcases p5003_3 (m.d 0 4) (by simp) with h5029 | h5029
                                · rcases p5003_3 (m.d 0 5) (by simp) with h5030 | h5030
                                  · linarith only [h4989, h5030, hlam]
                                  · rcases h2bigk with h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c | h5032c
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [hlam, p5032_0]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [h0, hlam, p5032_1]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [h5000, h5002, hc45, hlam, hphi, ht0b, ht5b, p5032_1, u0elo1]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [h4998, h5000, h5002, hc45, hlam, hphi, ht0b, ht5b, p5032_1, u0elo1]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      rcases p5032_3 (m.d 0 2) (by simp) with h5037 | h5037
                                      · rcases p5032_3 (m.d 1 2) (by simp) with h5038 | h5038
                                        · rcases p5032_3 (m.d 2 3) (by simp) with h5039 | h5039
                                          · linarith only [h4613, h5039, hlam]
                                          · linarith only [h5000, h5039, hlam]
                                        · linarith only [h4993, h5038, hlam]
                                      · linarith only [h5037, hlam, p5032_0]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [h0, h4611, h4612, h4616, h4993, h5000, h5002, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5003_1, p5032_1]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [hlam, p5032_0]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      rcases p5032_3 (m.d 0 2) (by simp) with h5046 | h5046
                                      · linarith only [h0, h5046, hlam]
                                      · linarith only [h4613, h5046, hlam]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      rcases p5032_3 (m.d 0 2) (by simp) with h5049 | h5049
                                      · linarith only [h0, h5049, hlam]
                                      · linarith only [h4614, h5049, hlam]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [h0, h4611, h4612, h4616, h4993, hlam, p5003_1, p5032_2]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [h4613, hlam, p5032_0]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [h4991, hlam, p5032_0]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [hlam, p5032_0]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [h4998, hlam, p5032_0]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [h4610, h4991, h5000, h5002, hc45, hlam, hphi, ht0b, ht5b, p5032_1, u0elo0]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [h4614, hlam, p5032_0]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [h4992, hlam, p5032_0]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [h0, h4611, h4612, h4616, h4992, h4993, h5000, h5002, hc23, hc34, hc45, hlam, hphi, ht0b, ht5b, p5003_1, p5032_1, u0elo1]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [hlam, p5032_0]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [h0, h4611, h4992, h5000, h5002, hc45, hlam, hphi, ht0b, ht5b, p5032_1, u0elo1]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [h4615, hlam, p5032_0]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [h4993, hlam, p5032_0]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [h5000, hlam, p5032_1]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [h5001, hlam, p5032_0]
                                    · have p5032_0 := h5032c.1
                                      have p5032_1 := h5032c.2.1
                                      have p5032_2 := h5032c.2.2.1
                                      have p5032_3 := h5032c.2.2.2
                                      linarith only [hlam, p5032_0]
                                · linarith only [h4990, h5029, hlam]
                              · linarith only [h4989, h5028, hlam]
                            · linarith only [h4615, h5027, hlam]
                          · linarith only [h4612, h5026, hlam]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [h4611, hlam, p5003_0]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [h4614, hlam, p5003_0]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [h0, h4611, h4613, h5000, h5002, hc45, hlam, hphi, ht0b, ht5b, p5003_1, u0elo1]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [hlam, p5003_0]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          rcases p5003_3 (m.d 0 1) (by simp) with h5076 | h5076
                          · rcases p5003_3 (m.d 0 2) (by simp) with h5077 | h5077
                            · rcases p5003_3 (m.d 0 3) (by simp) with h5078 | h5078
                              · linarith only [h4616, h5078, hlam]
                              · linarith only [h4989, h5078, hlam]
                            · linarith only [h4615, h5077, hlam]
                          · linarith only [h4612, h5076, hlam]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [h4612, hlam, p5003_0]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [h4615, hlam, p5003_1]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [h4989, hlam, p5003_0]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [h4990, hlam, p5003_1]
                        · have p5003_0 := h5003c.1
                          have p5003_1 := h5003c.2.1
                          have p5003_2 := h5003c.2.2.1
                          have p5003_3 := h5003c.2.2.2
                          linarith only [hlam, p5003_0]
                      · linarith only [h4616, h4990, h5002, hlam]
                    · linarith only [h0, h4611, h4997, h5001, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h4616, h4989, h5000, hc23, hc34, hlam, hphi]
              · linarith only [h0, h4611, h4990, h4994, h4996, h4997, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
            · linarith only [h4616, h4989, h4991, h4996, hc23, hc34, hlam, hphi]
        · linarith only [h0, h4615, h4993, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · linarith only [h0, h4614, h4992, hlam]
    · linarith only [h0, h4613, h4991, hlam]
  · linarith only [h4616, h4989, h4990, hlam]

end R2N4
