import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_28S10
import Jsp000404.R1LeavesN7_28S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1833 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2722 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3122 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3210 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h4271 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1833 := hg1833
  rcases m.htr 0 2 5 (by decide) (by decide) with h4607 | h4607
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4608 | h4608
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4609 | h4609
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4610 | h4610
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4611 | h4611
          · linarith only [h3210, h4607, h4611, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4613 | h4613
            · linarith only [h4271, h4607, h4611, h4613, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4615 | h4615
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4616 | h4616
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4617 | h4617
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4618 | h4618
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4619 | h4619
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4620 | h4620
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4621 | h4621
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4622 | h4622
                            · linarith only [h4608, h4622, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                            · rcases h0bigk with h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [hlam, p4624_0]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [h0, hlam, p4624_1]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [h1833, hlam, p4624_0]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [h2722, hlam, p4624_1]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [h3122, hlam, p4624_1]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [h0, h4613, h4619, hc01, hc23, hlam, hphi, ht12, p4624_1]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [hlam, p4624_0]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [h3210, hlam, p4624_0]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [h4271, hlam, p4624_1]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p4624_1, u0elo1, u5ehi0]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                rcases p4624_3 (m.d 0 1) (by simp) with h4635 | h4635
                                · linarith only [h1833, h4635, hlam]
                                · rcases p4624_3 (m.d 0 2) (by simp) with h4637 | h4637
                                  · linarith only [h3210, h4637, hlam]
                                  · linarith only [h0, h4637, hlam]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [h4607, h4621, h4622, hc34, hlam, hphi, ht0b, ht45, ht5b, p4624_1, u0elo2]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [hlam, p4624_0]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [h4271, h4607, h4621, h4622, hc34, hlam, hphi, ht0b, ht45, ht5b, p4624_1, u0elo2]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p4624_1, u0elo2, u5ehi0]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                rcases p4624_3 (m.d 0 1) (by simp) with h4644 | h4644
                                · linarith only [h2722, h4644, hlam]
                                · rcases p4624_3 (m.d 0 2) (by simp) with h4646 | h4646
                                  · linarith only [h4271, h4646, hlam]
                                  · linarith only [h0, h4646, hlam]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [h4607, h4608, h4621, h4622, hc34, hlam, hphi, ht0b, ht45, ht5b, p4624_1, u0elo2]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [h4608, hlam, p4624_0]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [hlam, p4624_0]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [h4607, h4608, h4621, h4622, hc34, hlam, hphi, ht0b, ht45, ht5b, p4624_1, u0elo2]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [h0, h4607, h4613, h4619, hc01, hc23, hlam, hphi, ht12, p4624_1]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [h4607, hlam, p4624_1]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [h4609, hlam, p4624_0]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [h4610, hlam, p4624_1]
                              · have p4624_0 := h4624c.1
                                have p4624_1 := h4624c.2.1
                                have p4624_2 := h4624c.2.2.1
                                have p4624_3 := h4624c.2.2.2
                                linarith only [hlam, p4624_0]
                          · linarith only [h0, h4613, h4621, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h3210, h4607, h4620, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h0, h4607, h4611, h4619, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h2722, h4271, h4607, h4610, h4618, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
                  · linarith only [h0, h1833, h4607, h4609, h4611, h4617, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h1833, h4608, h4616, hlam]
              · linarith only [h0, h4607, h4615, hlam]
        · linarith only [h4271, h4607, h4610, hlam]
      · linarith only [h3210, h4607, h4609, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4667 | h4667
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4668 | h4668
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4669 | h4669
          · linarith only [h3210, h4607, h4669, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4671 | h4671
            · linarith only [h4271, h4607, h4669, h4671, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4673 | h4673
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4674 | h4674
                · linarith only [h3210, h4607, h4608, h4674, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4676 | h4676
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4677 | h4677
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4678 | h4678
                      · linarith only [h0, h4669, h4674, h4678, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h3210, h4607, h4678, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h0, h4607, h4668, h4669, h4674, h4677, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
                  · linarith only [h0, h4607, h4667, h4669, h4676, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
              · linarith only [h0, h4607, h4673, hlam]
        · linarith only [h3210, h4607, h4608, h4668, hlam]
      · linarith only [h3210, h4607, h4667, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4686 | h4686
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4687 | h4687
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4688 | h4688
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4689 | h4689
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4690 | h4690
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4691 | h4691
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4692 | h4692
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4693 | h4693
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4694 | h4694
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4695 | h4695
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4696 | h4696
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4697 | h4697
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4698 | h4698
                            · linarith only [h4686, h4698, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                            · rcases h0bigk with h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c | h4700c
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [hlam, p4700_0]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h0, hlam, p4700_1]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h1833, hlam, p4700_0]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h2722, hlam, p4700_1]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h3122, hlam, p4700_1]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h4607, h4691, hc01, hc15, hlam, hphi, p4700_1]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [hlam, p4700_0]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h3210, hlam, p4700_0]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h4271, hlam, p4700_1]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h4607, hlam, p4700_0]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h3210, h4689, hc01, hc12, hlam, hphi, p4700_1]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h0, h3210, h4689, hc01, hc12, hlam, hphi, p4700_1]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [hlam, p4700_0]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h3210, h4688, h4689, h4698, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4700_1]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h3210, h4688, h4689, h4698, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4700_1]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h3210, h4686, h4689, hc01, hc12, hlam, hphi, p4700_1]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h0, h3210, h4686, h4689, hc01, hc12, hlam, hphi, p4700_1]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h4686, hlam, p4700_0]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [hlam, p4700_0]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h3210, h4686, h4688, h4689, h4698, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4700_1]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h3210, h4687, h4689, hc01, hc12, hlam, hphi, p4700_1]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h0, h3210, h4687, h4689, hc01, hc12, hlam, hphi, p4700_1]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h4687, hlam, p4700_0]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [h4688, hlam, p4700_1]
                              · have p4700_0 := h4700c.1
                                have p4700_1 := h4700c.2.1
                                have p4700_2 := h4700c.2.2.1
                                have p4700_3 := h4700c.2.2.2
                                linarith only [hlam, p4700_0]
                          · linarith only [h4271, h4688, h4697, hlam]
                        · linarith only [h3210, h4687, h4696, hlam]
                      · linarith only [h3210, h4686, h4695, hlam]
                    · linarith only [h4271, h4688, h4690, h4694, hlam]
                  · linarith only [h1833, h4687, h4693, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h3210, h4686, h4689, h4692, hlam]
              · linarith only [h3210, h4687, h4689, h4691, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · linarith only [h3210, h4686, h4688, h4689, h4690, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4734 | h4734
            · linarith only [h0, h4271, h4689, h4734, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4736 | h4736
              · linarith only [h0, h4607, h4689, h4736, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4738 | h4738
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4739 | h4739
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4740 | h4740
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4741 | h4741
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4742 | h4742
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4743 | h4743
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4744 | h4744
                            · linarith only [h4686, h4744, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                            · rcases h0bigk with h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c | h4746c
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [hlam, p4746_0]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [h0, hlam, p4746_1]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [h1833, hlam, p4746_0]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [h2722, hlam, p4746_1]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [h3122, hlam, p4746_1]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [h0, h4736, h4741, h4743, hc01, hc23, hlam, hphi, ht12, p4746_1]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [hlam, p4746_0]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [h3210, hlam, p4746_0]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [h4271, hlam, p4746_1]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [h4607, hlam, p4746_0]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                rcases p4746_3 (m.d 0 1) (by simp) with h4757 | h4757
                                · linarith only [h1833, h4757, hlam]
                                · rcases p4746_3 (m.d 0 2) (by simp) with h4759 | h4759
                                  · linarith only [h3210, h4759, hlam]
                                  · linarith only [h0, h4759, hlam]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                rcases p4746_3 (m.d 0 1) (by simp) with h4762 | h4762
                                · linarith only [h1833, h4762, hlam]
                                · rcases p4746_3 (m.d 0 2) (by simp) with h4764 | h4764
                                  · linarith only [h3210, h4764, hlam]
                                  · rcases p4746_3 (m.d 0 3) (by simp) with h4766 | h4766
                                    · rcases p4746_3 (m.d 0 4) (by simp) with h4767 | h4767
                                      · linarith only [h4686, h4767, hlam]
                                      · linarith only [h4271, h4767, hlam]
                                    · linarith only [h3210, h4766, hlam]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [hlam, p4746_0]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [h4688, h4744, hc34, hlam, hphi, ht0b, ht45, ht5b, p4746_1, u0elo2]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p4746_1, u0elo2, u5ehi0]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                rcases p4746_3 (m.d 0 1) (by simp) with h4774 | h4774
                                · linarith only [h2722, h4774, hlam]
                                · rcases p4746_3 (m.d 0 2) (by simp) with h4776 | h4776
                                  · linarith only [h4271, h4776, hlam]
                                  · linarith only [h0, h4776, hlam]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                rcases p4746_3 (m.d 0 1) (by simp) with h4779 | h4779
                                · linarith only [h2722, h4779, hlam]
                                · rcases p4746_3 (m.d 0 2) (by simp) with h4781 | h4781
                                  · linarith only [h4271, h4781, hlam]
                                  · rcases p4746_3 (m.d 0 3) (by simp) with h4783 | h4783
                                    · rcases p4746_3 (m.d 0 4) (by simp) with h4784 | h4784
                                      · rcases p4746_3 (m.d 0 5) (by simp) with h4785 | h4785
                                        · linarith only [h4688, h4785, hlam]
                                        · linarith only [h4607, h4785, hlam]
                                      · linarith only [h4271, h4784, hlam]
                                    · linarith only [h3210, h4783, hlam]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [h4686, hlam, p4746_0]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [hlam, p4746_0]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [h4686, h4688, h4744, hc34, hlam, hphi, ht0b, ht45, ht5b, p4746_1, u0elo2]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                rcases p4746_3 (m.d 0 1) (by simp) with h4793 | h4793
                                · linarith only [h3122, h4793, hlam]
                                · rcases p4746_3 (m.d 0 2) (by simp) with h4795 | h4795
                                  · linarith only [h4607, h4795, hlam]
                                  · linarith only [h0, h4795, hlam]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                rcases p4746_3 (m.d 0 1) (by simp) with h4798 | h4798
                                · linarith only [h3122, h4798, hlam]
                                · rcases p4746_3 (m.d 0 2) (by simp) with h4800 | h4800
                                  · linarith only [h4607, h4800, hlam]
                                  · rcases p4746_3 (m.d 0 3) (by simp) with h4802 | h4802
                                    · rcases p4746_3 (m.d 0 4) (by simp) with h4803 | h4803
                                      · rcases p4746_3 (m.d 0 5) (by simp) with h4804 | h4804
                                        · rcases h2bigk with h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [hlam, p4805_0]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [h0, hlam, p4805_1]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [h3210, hlam, p4805_0]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [h4271, hlam, p4805_0]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [h4607, hlam, p4805_0]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [h0, h4736, h4741, h4743, hc01, hc23, hlam, hphi, ht12, p4805_1]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [hlam, p4805_0]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [h4689, hlam, p4805_0]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [h4734, hlam, p4805_0]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [h4736, hlam, p4805_0]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            rcases p4805_3 (m.d 0 2) (by simp) with h4816 | h4816
                                            · linarith only [h4816, hlam, p4805_0]
                                            · rcases p4805_3 (m.d 1 2) (by simp) with h4818 | h4818
                                              · linarith only [h4689, h4818, hlam]
                                              · linarith only [h0, h4818, hlam]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p4805_1]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [hlam, p4805_0]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [h0, h4271, hc01, hc23, hlam, hphi, ht12, p4805_1]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [h0, h4607, hc01, hc23, hlam, hphi, ht12, p4805_1]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            rcases p4805_3 (m.d 0 2) (by simp) with h4825 | h4825
                                            · linarith only [h4825, hlam, p4805_0]
                                            · rcases p4805_3 (m.d 1 2) (by simp) with h4827 | h4827
                                              · linarith only [h4734, h4827, hlam]
                                              · linarith only [h0, h4827, hlam]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p4805_1]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [h4741, hlam, p4805_1]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [hlam, p4805_0]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [h0, h3122, h4736, h4741, hc01, hc23, hlam, hphi, ht12, p4746_1, p4805_1]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            rcases p4805_3 (m.d 0 2) (by simp) with h4834 | h4834
                                            · linarith only [h4834, hlam, p4805_0]
                                            · rcases p4805_3 (m.d 1 2) (by simp) with h4836 | h4836
                                              · linarith only [h4736, h4836, hlam]
                                              · linarith only [h0, h4836, hlam]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p4805_1]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [h4742, hlam, p4805_1]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [h4743, hlam, p4805_0]
                                          · have p4805_0 := h4805c.1
                                            have p4805_1 := h4805c.2.1
                                            have p4805_2 := h4805c.2.2.1
                                            have p4805_3 := h4805c.2.2.2
                                            linarith only [hlam, p4805_0]
                                        · linarith only [h4607, h4804, hlam]
                                      · linarith only [h4271, h4803, hlam]
                                    · linarith only [h3210, h4802, hlam]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [h4687, hlam, p4746_0]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [h4688, hlam, p4746_1]
                              · have p4746_0 := h4746c.1
                                have p4746_1 := h4746c.2.1
                                have p4746_2 := h4746c.2.2.1
                                have p4746_3 := h4746c.2.2.2
                                linarith only [hlam, p4746_0]
                          · linarith only [h4271, h4688, h4743, hlam]
                        · linarith only [h3210, h4687, h4742, hlam]
                      · linarith only [h0, h4689, h4741, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h2722, h4688, h4740, hlam]
                  · linarith only [h1833, h4687, h4739, hlam]
                · linarith only [h1833, h4686, h4738, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4855 | h4855
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4856 | h4856
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4857 | h4857
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4858 | h4858
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4859 | h4859
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4860 | h4860
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4861 | h4861
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4862 | h4862
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4863 | h4863
                          · linarith only [h2722, h4688, h4856, h4863, hc01, hc12, hlam, hphi]
                          · linarith only [h0, h4271, h4855, h4858, h4860, h4863, hc01, hc12, hlam, hphi]
                        · linarith only [h3210, h4687, h4862, hlam]
                      · linarith only [h3210, h4686, h4687, h4861, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4868 | h4868
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4869 | h4869
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4870 | h4870
                          · linarith only [h2722, h4860, h4870, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4872 | h4872
                            · linarith only [h0, h4271, h4686, h4856, h4860, h4872, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases h0bigk with h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c | h4874c
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [hlam, p4874_0]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h0, hlam, p4874_1]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h1833, hlam, p4874_0]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h2722, hlam, p4874_1]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h3122, hlam, p4874_1]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h4271, h4856, hc01, hc14, hlam, hphi, p4874_1]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [hlam, p4874_0]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h3210, hlam, p4874_0]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h4271, hlam, p4874_1]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h4607, hlam, p4874_0]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h3210, h4855, hc01, hc12, hlam, hphi, p4874_1]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h0, h3210, h4855, hc01, hc12, hlam, hphi, p4874_1]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [hlam, p4874_0]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h2722, h3210, h4855, hc01, hc12, hlam, hphi, p4874_1]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h3210, h4855, hc12, hlam, hphi, ht01, ht0b, ht5b, p4874_1, u5ehi0]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h2722, h4860, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4874_1]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h0, h4271, h4856, h4860, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4874_1]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h4686, hlam, p4874_0]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [hlam, p4874_0]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h4688, hlam, p4874_0]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h3210, h4687, h4855, hc01, hc12, hlam, hphi, p4874_1]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h0, h3210, h4687, h4855, hc01, hc12, hlam, hphi, p4874_1]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h4687, hlam, p4874_0]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [h2722, h3210, h4687, h4855, hc01, hc12, hlam, hphi, p4874_1]
                              · have p4874_0 := h4874c.1
                                have p4874_1 := h4874c.2.1
                                have p4874_2 := h4874c.2.2.1
                                have p4874_3 := h4874c.2.2.2
                                linarith only [hlam, p4874_0]
                        · linarith only [h3210, h4687, h4869, hlam]
                      · linarith only [h3210, h4686, h4687, h4868, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                  · linarith only [h1833, h4687, h4859, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h3210, h4686, h4855, h4858, hlam]
              · linarith only [h3210, h4687, h4855, h4857, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · linarith only [h3210, h4687, h4855, h4856, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4906 | h4906
            · linarith only [h0, h4271, h4855, h4906, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4908 | h4908
              · linarith only [h0, h4607, h4855, h4908, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4910 | h4910
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4911 | h4911
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4912 | h4912
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4913 | h4913
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4914 | h4914
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4915 | h4915
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4916 | h4916
                            · linarith only [h4686, h4688, h4916, hlam]
                            · rcases h0bigk with h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c | h4918c
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [hlam, p4918_0]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [h0, hlam, p4918_1]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [h1833, hlam, p4918_0]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [h2722, hlam, p4918_1]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [h3122, hlam, p4918_1]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [h4271, h4688, h4910, h4912, hc01, hc13, hlam, hphi, p4918_1]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [hlam, p4918_0]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [h3210, hlam, p4918_0]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [h4271, hlam, p4918_1]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [h4607, hlam, p4918_0]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                rcases p4918_3 (m.d 0 1) (by simp) with h4929 | h4929
                                · linarith only [h1833, h4929, hlam]
                                · rcases p4918_3 (m.d 0 2) (by simp) with h4931 | h4931
                                  · linarith only [h3210, h4931, hlam]
                                  · linarith only [h0, h4931, hlam]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                rcases p4918_3 (m.d 0 1) (by simp) with h4934 | h4934
                                · linarith only [h1833, h4934, hlam]
                                · rcases p4918_3 (m.d 0 2) (by simp) with h4936 | h4936
                                  · linarith only [h3210, h4936, hlam]
                                  · rcases p4918_3 (m.d 0 3) (by simp) with h4938 | h4938
                                    · rcases p4918_3 (m.d 0 4) (by simp) with h4939 | h4939
                                      · linarith only [h4686, h4939, hlam]
                                      · linarith only [h4271, h4939, hlam]
                                    · linarith only [h3210, h4938, hlam]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [hlam, p4918_0]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                rcases p4918_3 (m.d 0 1) (by simp) with h4944 | h4944
                                · linarith only [h1833, h4944, hlam]
                                · rcases p4918_3 (m.d 0 2) (by simp) with h4946 | h4946
                                  · linarith only [h3210, h4946, hlam]
                                  · rcases p4918_3 (m.d 0 3) (by simp) with h4948 | h4948
                                    · rcases p4918_3 (m.d 0 4) (by simp) with h4949 | h4949
                                      · linarith only [h4686, h4949, hlam]
                                      · rcases p4918_3 (m.d 0 5) (by simp) with h4951 | h4951
                                        · linarith only [h4687, h4951, hlam]
                                        · linarith only [h4688, h4951, hlam]
                                    · linarith only [h4686, h4948, hlam]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p4918_1, u0elo2, u5ehi0]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [h4688, h4855, h4910, h4912, hc01, hc23, hlam, hphi, ht12, p4918_1]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [h0, h4688, h4855, h4910, h4912, hc01, hc23, hlam, hphi, ht12, p4918_1]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [h4686, hlam, p4918_0]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [hlam, p4918_0]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [h4688, hlam, p4918_0]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [h4688, h4855, h4910, h4912, hc01, hc23, hlam, hphi, ht12, p4918_1]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [h0, h4688, h4855, h4910, h4912, hc01, hc23, hlam, hphi, ht12, p4918_1]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [h4687, hlam, p4918_0]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [h2722, h4688, h4855, h4910, h4912, hc01, hc23, hlam, hphi, ht12, p4918_1]
                              · have p4918_0 := h4918c.1
                                have p4918_1 := h4918c.2.1
                                have p4918_2 := h4918c.2.2.1
                                have p4918_3 := h4918c.2.2.2
                                linarith only [hlam, p4918_0]
                          · linarith only [h0, h4271, h4855, h4910, h4912, h4915, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h1833, h4687, h4855, h4914, hlam]
                      · linarith only [h1833, h4686, h4688, h4855, h4912, h4913, hc01, hc14, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4969 | h4969
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4970 | h4970
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4971 | h4971
                          · linarith only [h2722, h4912, h4969, h4971, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h4906, h4971, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h3210, h4687, h4970, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1833, h4686, h4855, h4969, hlam]
                  · linarith only [h1833, h4687, h4911, hlam]
                · linarith only [h1833, h4686, h4910, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4978 | h4978
        · linarith only [h4686, h4687, h4978, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4980 | h4980
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4981 | h4981
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4982 | h4982
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4983 | h4983
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4984 | h4984
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4985 | h4985
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4986 | h4986
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4987 | h4987
                        · linarith only [h4686, h4687, h4980, h4987, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h3210, h4980, h4984, h4987, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h3210, h4686, h4986, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4991 | h4991
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4992 | h4992
                        · linarith only [h4686, h4687, h4980, h4992, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h3210, h4980, h4984, h4992, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h3210, h4686, h4687, h4980, h4984, h4991, hc01, hc12, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4996 | h4996
                    · linarith only [h2722, h4978, h4983, h4984, h4996, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4998 | h4998
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4999 | h4999
                        · linarith only [h4271, h4981, h4983, h4984, h4999, hc02, hc23, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5001 | h5001
                          · linarith only [h4981, h4996, h5001, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5003 | h5003
                            · linarith only [h0, h4271, h4686, h4981, h4996, h5003, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                            · rcases h0bigk with h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c | h5005c
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [hlam, p5005_0]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h0, hlam, p5005_1]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h1833, hlam, p5005_0]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h2722, hlam, p5005_1]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h3122, hlam, p5005_1]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h4271, h4981, hc01, hc14, hlam, hphi, p5005_1]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [hlam, p5005_0]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h3210, hlam, p5005_0]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h4271, hlam, p5005_1]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h4607, hlam, p5005_0]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h3210, h4980, h4984, h5003, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5005_1]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h3210, h4980, h4984, h5003, hc02, hc45, hlam, hphi, ht23, ht34, p5005_1]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [hlam, p5005_0]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h3210, h4980, h4984, h5003, hc04, hc45, hlam, hphi, p5005_1]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h4687, hlam, p5005_1]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h3210, h4686, h4980, h4984, h5003, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5005_1]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h0, h3210, h4686, h4980, h4984, h5003, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5005_1]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h4686, hlam, p5005_0]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [hlam, p5005_0]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h4978, hlam, p5005_0]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h4607, h4982, hc01, hc12, hlam, hphi, p5005_1]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h0, h4607, h4982, hc01, hc12, hlam, hphi, p5005_1]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h4607, h4686, h4982, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5005_1]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [h2722, h4607, h4982, hc01, hc12, hlam, hphi, p5005_1]
                              · have p5005_0 := h5005c.1
                                have p5005_1 := h5005c.2.1
                                have p5005_2 := h5005c.2.2.1
                                have p5005_3 := h5005c.2.2.2
                                linarith only [hlam, p5005_0]
                      · linarith only [h0, h3210, h4686, h4998, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h3210, h4686, h4980, h4983, hlam]
              · linarith only [h0, h3210, h4980, h4982, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h3210, h4980, h4981, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5035 | h5035
            · linarith only [h4271, h4980, h5035, hc02, hc23, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5037 | h5037
              · linarith only [h0, h4607, h4980, h5037, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5039 | h5039
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5040 | h5040
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5041 | h5041
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5042 | h5042
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5043 | h5043
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5044 | h5044
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5045 | h5045
                            · linarith only [h0, h4271, h4686, h4687, h4978, h4980, h5040, h5045, hc01, hc23, hlam, hphi, ht12]
                            · rcases h0bigk with h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c | h5047c
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [hlam, p5047_0]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h0, hlam, p5047_1]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h1833, hlam, p5047_0]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h2722, hlam, p5047_1]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h3122, hlam, p5047_1]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h0, h5037, h5042, h5044, hc01, hc23, hlam, hphi, ht12, p5047_1]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [hlam, p5047_0]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h3210, hlam, p5047_0]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h4271, hlam, p5047_1]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h4607, hlam, p5047_0]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h4687, h5035, h5041, h5042, h5045, hc01, hc23, hlam, hphi, ht12, p5047_1]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h4687, h5035, h5041, h5042, h5045, hc02, hc23, hlam, hphi, p5047_1]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [hlam, p5047_0]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h0, h4271, h4687, h5035, h5041, h5042, h5045, hc01, hc23, hlam, hphi, ht12, p5047_1]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h4687, hlam, p5047_1]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h4686, h4687, h5035, h5041, h5042, h5045, hc01, hc23, hlam, hphi, ht12, p5047_1]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h0, h4686, h4687, h5035, h5041, h5042, h5045, hc01, hc23, hlam, hphi, ht12, p5047_1]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h4686, hlam, p5047_0]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [hlam, p5047_0]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h4978, hlam, p5047_0]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h4687, h5035, h5041, h5042, h5045, hc01, hc23, hlam, hphi, ht12, p5047_1]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h0, h4687, h5035, h5041, h5042, h5045, hc01, hc23, hlam, hphi, ht12, p5047_1]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h4686, h4687, h5035, h5041, h5042, h5045, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5047_1]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [h2722, h4687, h5035, h5041, h5042, h5045, hc01, hc23, hlam, hphi, ht12, p5047_1]
                              · have p5047_0 := h5047c.1
                                have p5047_1 := h5047c.2.1
                                have p5047_2 := h5047c.2.2.1
                                have p5047_3 := h5047c.2.2.2
                                linarith only [hlam, p5047_0]
                          · linarith only [h5035, h5041, h5044, hlam]
                        · linarith only [h0, h4271, h4978, h5035, h5041, h5042, h5043, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h4271, h4686, h4978, h4980, h5039, h5041, h5042, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5076 | h5076
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5077 | h5077
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5078 | h5078
                          · linarith only [h0, h5035, h5041, h5078, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h5035, h5078, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h4980, h5040, h5077, hlam]
                      · linarith only [h4686, h4687, h4980, h5040, h5076, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5083 | h5083
                    · linarith only [h4271, h4978, h5039, h5040, h5083, hc02, hc35, hlam, hphi, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5085 | h5085
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5086 | h5086
                        · linarith only [h0, h5035, h5039, h5040, h5086, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h4980, h5086, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h4686, h4980, h5085, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h1833, h4686, h5039, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5091 | h5091
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5092 | h5092
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5093 | h5093
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5094 | h5094
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5095 | h5095
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5096 | h5096
                · linarith only [h4686, h5091, h5096, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5098 | h5098
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5099 | h5099
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5100 | h5100
                      · linarith only [h1833, h5096, h5100, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5102 | h5102
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5103 | h5103
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5104 | h5104
                            · rcases h0bigk with h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c | h5105c
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [hlam, p5105_0]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h0, hlam, p5105_1]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h1833, hlam, p5105_0]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h2722, hlam, p5105_1]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h3122, hlam, p5105_1]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h3210, h5093, hc01, hc13, hlam, hphi, p5105_1]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [hlam, p5105_0]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h3210, hlam, p5105_0]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h4271, hlam, p5105_1]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h4607, hlam, p5105_0]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h1833, h5096, hc01, hc34, hlam, hphi, ht12, ht23, p5105_1]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h3210, h5093, h5096, hc02, hc34, hlam, hphi, ht23, p5105_1]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [hlam, p5105_0]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h4686, hlam, p5105_1]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h3210, h5093, h5096, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5105_1, u5ehi0]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h4271, h5094, hc01, hc12, hlam, hphi, p5105_1]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h0, h4271, h5094, hc01, hc12, hlam, hphi, p5105_1]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h4271, h5091, h5094, hc12, hlam, hphi, ht01, ht0b, ht5b, p5105_1, u5ehi3]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [hlam, p5105_0]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h4271, h5091, h5094, h5104, hc12, hlam, hphi, ht01, ht0b, ht5b, p5105_1, u5ehi4]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h3122, h5096, h5098, hc01, hc34, hlam, hphi, ht12, ht23, p5105_1]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h0, h4607, h5095, h5096, h5098, hc01, hc34, hlam, hphi, ht12, ht23, p5105_1]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h5091, hlam, p5105_0]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [h5092, hlam, p5105_1]
                              · have p5105_0 := h5105c.1
                                have p5105_1 := h5105c.2.1
                                have p5105_2 := h5105c.2.2.1
                                have p5105_3 := h5105c.2.2.2
                                linarith only [hlam, p5105_0]
                            · linarith only [h1833, h5096, h5104, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h4271, h5092, h5103, hlam]
                        · linarith only [h3210, h5091, h5102, hlam]
                    · linarith only [h4271, h5092, h5094, h5099, hlam]
                  · linarith only [h3210, h5091, h5093, h5098, hlam]
              · linarith only [h4271, h5092, h5094, h5095, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · linarith only [h3210, h5091, h5093, h5094, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5138 | h5138
            · linarith only [h0, h4271, h5093, h5138, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5140 | h5140
              · linarith only [h0, h4607, h5093, h5140, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5142 | h5142
                · linarith only [h4686, h5091, h5142, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5144 | h5144
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5145 | h5145
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5146 | h5146
                      · linarith only [h0, h5140, h5142, h5144, h5146, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h5093, h5146, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1833, h5091, h5092, h5142, h5145, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                  · linarith only [h1833, h5091, h5144, hlam]
        · linarith only [h4686, h5091, h5092, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5152 | h5152
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5153 | h5153
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5154 | h5154
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5155 | h5155
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5156 | h5156
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5157 | h5157
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5158 | h5158
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5159 | h5159
                      · linarith only [h1833, h4686, h5153, h5159, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h3210, h5153, h5156, h5159, hc01, hc12, hlam, hphi]
                    · linarith only [h2722, h5152, h5158, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h3210, h4686, h5156, h5157, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5164 | h5164
                  · linarith only [h5091, h5156, h5164, hc03, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5166 | h5166
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5167 | h5167
                      · linarith only [h5153, h5156, h5167, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5169 | h5169
                        · linarith only [h5153, h5164, h5169, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5171 | h5171
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5172 | h5172
                            · rcases h0bigk with h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c | h5173c
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [hlam, p5173_0]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h0, hlam, p5173_1]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h1833, hlam, p5173_0]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h2722, hlam, p5173_1]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h3122, hlam, p5173_1]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h1833, h3210, h5164, h5172, hc01, hc34, hlam, hphi, ht12, ht23, p5173_1]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [hlam, p5173_0]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h3210, hlam, p5173_0]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h4271, hlam, p5173_1]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h4607, hlam, p5173_0]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h1833, h5164, h5172, hc01, hc34, hlam, hphi, ht12, ht23, p5173_1]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h1833, h5164, h5172, hc02, hc34, hlam, hphi, ht23, p5173_1]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [hlam, p5173_0]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h4686, hlam, p5173_1]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h5091, hlam, p5173_1]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h4271, h5154, hc01, hc12, hlam, hphi, p5173_1]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h0, h4271, h5154, hc01, hc12, hlam, hphi, p5173_1]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h1833, h4271, h5154, hc01, hc12, hlam, hphi, p5173_1]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [hlam, p5173_0]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h4271, h5152, h5154, hc12, hlam, hphi, ht01, ht0b, ht5b, p5173_1, u5ehi4]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h4607, h5154, h5171, hc01, hc12, hlam, hphi, p5173_1]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h0, h4607, h5154, h5171, hc01, hc12, hlam, hphi, p5173_1]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h0, h3210, h4607, h5154, h5171, hc01, hc12, hlam, hphi, p5173_1]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [h5152, hlam, p5173_1]
                              · have p5173_0 := h5173c.1
                                have p5173_1 := h5173c.2.1
                                have p5173_2 := h5173c.2.2.1
                                have p5173_3 := h5173c.2.2.2
                                linarith only [hlam, p5173_0]
                            · linarith only [h4686, h5152, h5172, hlam]
                          · linarith only [h4271, h5152, h5171, hlam]
                    · linarith only [h4271, h5152, h5154, h5166, hlam]
              · linarith only [h4271, h5152, h5154, h5155, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · linarith only [h0, h3210, h5153, h5154, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5204 | h5204
            · linarith only [h0, h4271, h5153, h5204, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5206 | h5206
              · linarith only [h0, h4607, h5153, h5206, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5208 | h5208
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5209 | h5209
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5210 | h5210
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5211 | h5211
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5212 | h5212
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5213 | h5213
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5214 | h5214
                            · rcases h0bigk with h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h0, hlam, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h1833, hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h2722, hlam, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h3122, hlam, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h0, h5206, h5211, h5213, hc01, hc23, hlam, hphi, ht12, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h3210, hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h4271, hlam, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h4607, hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h4686, h5208, hc01, hc13, hlam, hphi, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h4686, h5208, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h4686, hlam, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h5091, hlam, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h4686, h5208, hc01, hc13, hlam, hphi, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h0, h4686, h5208, hc01, hc13, hlam, hphi, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h1833, h4686, h5208, hc01, hc13, hlam, hphi, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h4686, h5208, hc13, hlam, hphi, ht01, ht0b, ht5b, p5215_1, u5ehi0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h5091, h5208, h5214, hc01, hc13, hlam, hphi, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h0, h5091, h5208, h5214, hc01, hc13, hlam, hphi, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h0, h3210, h5091, h5208, h5214, hc01, hc13, hlam, hphi, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h5152, hlam, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [hlam, p5215_0]
                            · linarith only [h4686, h5152, h5214, hlam]
                          · linarith only [h0, h4271, h5152, h5213, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h0, h3210, h4686, h5153, h5208, h5212, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h5153, h5208, h5211, hlam]
                    · linarith only [h2722, h5152, h5210, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h4686, h5152, h5208, h5209, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5247 | h5247
                  · linarith only [h0, h3210, h5091, h5208, h5247, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5249 | h5249
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5250 | h5250
                      · linarith only [h1833, h5208, h5250, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h5153, h5250, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h2722, h5152, h5249, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5254 | h5254
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5255 | h5255
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5256 | h5256
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5257 | h5257
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5258 | h5258
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5259 | h5259
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5260 | h5260
                      · linarith only [h0, h3210, h4686, h5254, h5260, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h3210, h5254, h5257, h5260, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5263 | h5263
                      · linarith only [h0, h3210, h4686, h5254, h5263, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h3210, h5254, h5257, h5263, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h3210, h4686, h5257, h5258, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5267 | h5267
                  · linarith only [h0, h3210, h5091, h5257, h5267, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5269 | h5269
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5270 | h5270
                      · linarith only [h1833, h5257, h5270, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5272 | h5272
                        · linarith only [h5254, h5267, h5272, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5274 | h5274
                          · linarith only [h0, h3210, h4686, h5152, h5255, h5274, hc01, hc12, hlam, hphi]
                          · linarith only [h0, h4271, h5257, h5269, h5274, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5277 | h5277
                      · linarith only [h0, h3210, h4686, h5254, h5267, h5277, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5279 | h5279
                        · linarith only [h0, h3210, h5091, h5254, h5257, h5269, h5279, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5281 | h5281
                          · linarith only [h1833, h5257, h5269, h5281, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5283 | h5283
                            · linarith only [h0, h3210, h5254, h5257, h5269, h5283, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h3210, h5254, h5257, h5283, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h3210, h5254, h5256, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h3210, h5254, h5255, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5288 | h5288
            · linarith only [h0, h4271, h5254, h5288, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5290 | h5290
              · linarith only [h0, h4607, h5254, h5290, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5292 | h5292
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5293 | h5293
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5294 | h5294
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5295 | h5295
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5296 | h5296
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5297 | h5297
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5298 | h5298
                            · linarith only [h0, h3210, h4686, h5152, h5292, h5298, hc01, hc13, hlam, hphi]
                            · linarith only [h0, h3210, h4686, h5294, h5298, hc01, hc14, hlam, hphi]
                          · linarith only [h5288, h5294, h5297, hlam]
                        · linarith only [h5254, h5293, h5296, hlam]
                      · linarith only [h0, h3210, h5091, h5254, h5293, h5295, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5304 | h5304
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5305 | h5305
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5306 | h5306
                          · linarith only [h2722, h5294, h5306, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h5288, h5306, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h5254, h5293, h5305, hlam]
                      · linarith only [h0, h3210, h5091, h5254, h5292, h5293, h5304, hc01, hc14, hlam, hphi]
                  · linarith only [h0, h3210, h4686, h5292, h5293, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5312 | h5312
                  · linarith only [h0, h3210, h5091, h5292, h5312, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5314 | h5314
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5315 | h5315
                      · linarith only [h1833, h5292, h5315, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h5254, h5315, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5318 | h5318
                      · linarith only [h1833, h5292, h5318, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h5254, h5318, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1833 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2722 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3122 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3210 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1833 := hg1833
  rcases m.htr 0 2 4 (by decide) (by decide) with h4271 | h4271
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1833 h2722 h3122 h3210 h4271
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1833 h2722 h3122 h3210 h4271

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1833 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2722 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3122 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1833 := hg1833
  rcases m.htr 0 2 3 (by decide) (by decide) with h3210 | h3210
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1833 h2722 h3122 h3210
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1833 h2722 h3122 h3210

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1833 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2722 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1833 := hg1833
  rcases m.htr 0 1 5 (by decide) (by decide) with h3122 | h3122
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1833 h2722 h3122
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1833 h2722 h3122

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1833 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1833 := hg1833
  rcases m.htr 0 1 4 (by decide) (by decide) with h2722 | h2722
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x0 m hb0 hb2 hb3 hb5 hg0 hg1833 h2722
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1 m hb0 hb2 hb3 hb5 hg0 hg1833 h2722

end R2N4
