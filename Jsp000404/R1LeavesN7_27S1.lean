import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h713 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h743 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h744 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h745 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h746 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h748 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h750 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h752 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 3 5 (by decide) (by decide) with h753 | h753
  · rcases m.htr 1 4 5 (by decide) (by decide) with h754 | h754
    · rcases m.htr 2 3 4 (by decide) (by decide) with h755 | h755
      · rcases m.htr 2 3 5 (by decide) (by decide) with h756 | h756
        · rcases m.htr 2 4 5 (by decide) (by decide) with h757 | h757
          · rcases m.htr 3 4 5 (by decide) (by decide) with h758 | h758
            · linarith only [h1, h752, h758, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · linarith only [h1, h752, h754, h758, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
          · linarith only [h2, h600, h754, h757, hlam]
        · linarith only [h1, h3, h4, h752, h753, h754, h756, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
      · linarith only [h1, h4, h752, h755, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h764 | h764
      · rcases m.htr 2 3 5 (by decide) (by decide) with h765 | h765
        · rcases m.htr 2 4 5 (by decide) (by decide) with h766 | h766
          · rcases m.htr 3 4 5 (by decide) (by decide) with h767 | h767
            · linarith only [h752, h754, h767, hlam]
            · rcases h0bigk with h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c | h769c
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [hlam, p769_0]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                rcases p769_3 (m.d 0 1) (by simp) with h771 | h771
                · rcases p769_3 (m.d 0 2) (by simp) with h772 | h772
                  · linarith only [h0, h772, hlam]
                  · rcases p769_3 (m.d 0 3) (by simp) with h774 | h774
                    · linarith only [h1, h774, hlam]
                    · linarith only [h4, h774, hlam]
                · linarith only [h0, h771, hlam]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [h743, h745, h752, h754, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p769_1, u3ehi3]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [h745, h752, h754, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p769_1, u3ehi3]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [h745, h752, h754, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p769_1, u3ehi3]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [h0, hlam, p769_0]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [hlam, p769_0]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [h4, hlam, p769_0]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [h600, hlam, p769_1]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [h713, hlam, p769_0]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [h1, hlam, p769_1]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                rcases p769_3 (m.d 0 1) (by simp) with h787 | h787
                · rcases p769_3 (m.d 0 2) (by simp) with h788 | h788
                  · linarith only [h4, h788, hlam]
                  · rcases p769_3 (m.d 0 3) (by simp) with h790 | h790
                    · rcases p769_3 (m.d 0 4) (by simp) with h791 | h791
                      · linarith only [h743, h791, hlam]
                      · linarith only [h600, h791, hlam]
                    · linarith only [h4, h790, hlam]
                · linarith only [h0, h787, hlam]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [hlam, p769_0]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [h4, h745, h752, h754, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p769_1, u3ehi3]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [h4, h745, h752, h754, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p769_1, u3ehi3]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [h2, hlam, p769_0]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                rcases p769_3 (m.d 0 1) (by simp) with h800 | h800
                · rcases p769_3 (m.d 0 2) (by simp) with h801 | h801
                  · linarith only [h600, h801, hlam]
                  · rcases p769_3 (m.d 0 3) (by simp) with h803 | h803
                    · rcases p769_3 (m.d 0 4) (by simp) with h804 | h804
                      · rcases p769_3 (m.d 0 5) (by simp) with h805 | h805
                        · linarith only [h745, h805, hlam]
                        · linarith only [h713, h805, hlam]
                      · linarith only [h600, h804, hlam]
                    · linarith only [h4, h803, hlam]
                · linarith only [h0, h800, hlam]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [h743, hlam, p769_0]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [hlam, p769_0]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [h745, h752, h754, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p769_1, u3ehi3]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [h3, hlam, p769_0]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                rcases p769_3 (m.d 0 1) (by simp) with h815 | h815
                · rcases p769_3 (m.d 0 2) (by simp) with h816 | h816
                  · linarith only [h713, h816, hlam]
                  · rcases p769_3 (m.d 0 3) (by simp) with h818 | h818
                    · rcases p769_3 (m.d 0 4) (by simp) with h819 | h819
                      · rcases p769_3 (m.d 0 5) (by simp) with h820 | h820
                        · rcases h0emin with h821 | h821 | h821 | h821 | h821
                          · rcases h2bigk with h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p769_1, p822_1]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h4, hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h600, hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h713, hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h0, hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h746, hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h748, hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h750, hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              rcases p822_3 (m.d 0 2) (by simp) with h833 | h833
                              · linarith only [h833, hlam, p822_0]
                              · rcases p822_3 (m.d 1 2) (by simp) with h835 | h835
                                · linarith only [h746, h835, hlam]
                                · rcases p822_3 (m.d 2 3) (by simp) with h837 | h837
                                  · rcases p822_3 (m.d 2 4) (by simp) with h838 | h838
                                    · linarith only [h764, h838, hlam]
                                    · linarith only [h600, h838, hlam]
                                  · linarith only [h837, hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              rcases p822_3 (m.d 0 2) (by simp) with h842 | h842
                              · linarith only [h4, h842, hlam]
                              · linarith only [h0, h842, hlam]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h600, hc02, hc23, hlam, hphi, p822_1]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h0, h713, hc12, hc23, hlam, hphi, p822_1]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              rcases p822_3 (m.d 0 2) (by simp) with h848 | h848
                              · linarith only [h848, hlam, p822_0]
                              · rcases p822_3 (m.d 1 2) (by simp) with h850 | h850
                                · linarith only [h748, h850, hlam]
                                · rcases p822_3 (m.d 2 3) (by simp) with h852 | h852
                                  · rcases p822_3 (m.d 2 4) (by simp) with h853 | h853
                                    · rcases p822_3 (m.d 2 5) (by simp) with h854 | h854
                                      · linarith only [h766, h854, hlam]
                                      · linarith only [h713, h854, hlam]
                                    · linarith only [h853, hlam, p822_0]
                                  · linarith only [h4, h852, hlam]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              rcases p822_3 (m.d 0 2) (by simp) with h859 | h859
                              · linarith only [h600, h859, hlam]
                              · linarith only [h0, h859, hlam]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h764, hlam, p822_1]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h0, h713, hc12, hc24, hlam, hphi, p769_1, p822_1]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              rcases p822_3 (m.d 0 2) (by simp) with h865 | h865
                              · linarith only [h865, hlam, p822_0]
                              · rcases p822_3 (m.d 1 2) (by simp) with h867 | h867
                                · linarith only [h750, h867, hlam]
                                · rcases p822_3 (m.d 2 3) (by simp) with h869 | h869
                                  · rcases p822_3 (m.d 2 4) (by simp) with h870 | h870
                                    · rcases p822_3 (m.d 2 5) (by simp) with h871 | h871
                                      · rcases h5bigk with h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [hlam, p872_0]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          rcases p872_3 (m.d 0 5) (by simp) with h874 | h874
                                          · rcases p872_3 (m.d 1 5) (by simp) with h875 | h875
                                            · linarith only [h3, h875, hlam]
                                            · rcases p872_3 (m.d 2 5) (by simp) with h877 | h877
                                              · rcases p872_3 (m.d 3 5) (by simp) with h878 | h878
                                                · linarith only [h744, h878, hlam]
                                                · rcases p872_3 (m.d 4 5) (by simp) with h880 | h880
                                                  · linarith only [h745, h880, hlam]
                                                  · linarith only [h754, h880, hlam]
                                              · linarith only [h750, h877, hlam]
                                          · linarith only [h3, h874, hlam]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [h713, hlam, p872_0]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          rcases p872_3 (m.d 0 5) (by simp) with h886 | h886
                                          · rcases p872_3 (m.d 1 5) (by simp) with h887 | h887
                                            · linarith only [h3, h887, hlam]
                                            · linarith only [h753, h887, hlam]
                                          · linarith only [h744, h886, hlam]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [h600, h745, h752, h754, h764, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p872_1, u3ehi3]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [h3, hlam, p872_0]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [hlam, p872_0]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [h750, hlam, p872_0]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [h3, h767, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p872_1, u3ehi3]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [h754, hlam, p872_1]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [h0, hc12, hc25, hlam, hphi, p769_1, p872_1]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          rcases p872_3 (m.d 0 5) (by simp) with h898 | h898
                                          · linarith only [h713, h898, hlam]
                                          · linarith only [h3, h898, hlam]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [hlam, p872_0]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          rcases p872_3 (m.d 0 5) (by simp) with h902 | h902
                                          · linarith only [h713, h902, hlam]
                                          · linarith only [h744, h902, hlam]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [h752, h754, h764, h766, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p872_1, u3ehi3]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [h744, hlam, p872_0]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [h753, hlam, p872_0]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [h765, hlam, p872_0]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [hlam, p872_0]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [h767, hlam, p872_1]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [h745, hlam, p872_0]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [h600, h745, h764, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p872_1, u5ehi1]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [h766, hlam, p872_0]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [h600, h745, h764, h767, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p872_1, u3ehi3]
                                        · have p872_0 := h872c.1
                                          have p872_1 := h872c.2.1
                                          have p872_2 := h872c.2.2.1
                                          have p872_3 := h872c.2.2.2
                                          linarith only [hlam, p872_0]
                                      · linarith only [h871, hlam, p822_0]
                                    · linarith only [h600, h870, hlam]
                                  · linarith only [h4, h869, hlam]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              rcases p822_3 (m.d 0 2) (by simp) with h919 | h919
                              · linarith only [h713, h919, hlam]
                              · linarith only [h0, h919, hlam]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h765, hlam, p822_1]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h766, hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [hlam, p822_0]
                          · linarith only [h821, hc05, hlam, p769_1]
                          · rcases h2bigk with h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [hlam, p926_0]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [h713, h764, h766, hc12, hc23, hlam, hphi, p769_1, p926_1]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [h4, hlam, p926_0]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [h600, hlam, p926_0]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [h713, hlam, p926_0]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [h0, hlam, p926_0]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [hlam, p926_0]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [h746, hlam, p926_0]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [h748, hlam, p926_0]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [h750, hlam, p926_0]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              rcases p926_3 (m.d 0 2) (by simp) with h937 | h937
                              · linarith only [h937, hlam, p926_0]
                              · rcases p926_3 (m.d 1 2) (by simp) with h939 | h939
                                · linarith only [h746, h939, hlam]
                                · rcases p926_3 (m.d 2 3) (by simp) with h941 | h941
                                  · rcases p926_3 (m.d 2 4) (by simp) with h942 | h942
                                    · linarith only [h764, h942, hlam]
                                    · linarith only [h600, h942, hlam]
                                  · linarith only [h941, hlam, p926_0]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              rcases p926_3 (m.d 0 2) (by simp) with h946 | h946
                              · linarith only [h4, h946, hlam]
                              · linarith only [h0, h946, hlam]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [hlam, p926_0]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [h713, h766, hc02, hc23, hlam, hphi, p769_1, p926_1]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [h0, h713, hc12, hc23, hlam, hphi, p769_1, p926_1]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              rcases p926_3 (m.d 0 2) (by simp) with h952 | h952
                              · linarith only [h952, hlam, p926_0]
                              · rcases p926_3 (m.d 1 2) (by simp) with h954 | h954
                                · linarith only [h748, h954, hlam]
                                · rcases p926_3 (m.d 2 3) (by simp) with h956 | h956
                                  · rcases p926_3 (m.d 2 4) (by simp) with h957 | h957
                                    · rcases p926_3 (m.d 2 5) (by simp) with h958 | h958
                                      · linarith only [h766, h958, hlam]
                                      · linarith only [h713, h958, hlam]
                                    · linarith only [h957, hlam, p926_0]
                                  · linarith only [h4, h956, hlam]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              rcases p926_3 (m.d 0 2) (by simp) with h963 | h963
                              · linarith only [h600, h963, hlam]
                              · linarith only [h0, h963, hlam]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [h764, hlam, p926_1]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [hlam, p926_0]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [h0, h713, hc12, hc24, hlam, hphi, p769_1, p926_1]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              rcases p926_3 (m.d 0 2) (by simp) with h969 | h969
                              · linarith only [h969, hlam, p926_0]
                              · rcases p926_3 (m.d 1 2) (by simp) with h971 | h971
                                · linarith only [h750, h971, hlam]
                                · rcases p926_3 (m.d 2 3) (by simp) with h973 | h973
                                  · rcases p926_3 (m.d 2 4) (by simp) with h974 | h974
                                    · rcases p926_3 (m.d 2 5) (by simp) with h975 | h975
                                      · rcases h5bigk with h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c | h976c
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [hlam, p976_0]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          rcases p976_3 (m.d 0 5) (by simp) with h978 | h978
                                          · rcases p976_3 (m.d 1 5) (by simp) with h979 | h979
                                            · linarith only [h3, h979, hlam]
                                            · rcases p976_3 (m.d 2 5) (by simp) with h981 | h981
                                              · rcases p976_3 (m.d 3 5) (by simp) with h982 | h982
                                                · linarith only [h744, h982, hlam]
                                                · rcases p976_3 (m.d 4 5) (by simp) with h984 | h984
                                                  · linarith only [h745, h984, hlam]
                                                  · linarith only [h754, h984, hlam]
                                              · linarith only [h750, h981, hlam]
                                          · linarith only [h3, h978, hlam]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [h713, hlam, p976_0]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          rcases p976_3 (m.d 0 5) (by simp) with h990 | h990
                                          · rcases p976_3 (m.d 1 5) (by simp) with h991 | h991
                                            · linarith only [h3, h991, hlam]
                                            · linarith only [h753, h991, hlam]
                                          · linarith only [h744, h990, hlam]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [h743, h745, h752, h754, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p976_1, u3ehi3]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [h3, hlam, p976_0]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [hlam, p976_0]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [h750, hlam, p976_0]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [h3, h767, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p976_1, u3ehi3]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [h754, hlam, p976_1]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [h0, hc12, hc25, hlam, hphi, p769_1, p976_1]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          rcases p976_3 (m.d 0 5) (by simp) with h1002 | h1002
                                          · linarith only [h1002, h713, hlam]
                                          · linarith only [h1002, h3, hlam]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [hlam, p976_0]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          rcases p976_3 (m.d 0 5) (by simp) with h1006 | h1006
                                          · linarith only [h1006, h713, hlam]
                                          · linarith only [h1006, h744, hlam]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [h752, h754, h764, h766, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p976_1, u3ehi3]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [h744, hlam, p976_0]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [h753, hlam, p976_0]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [h765, hlam, p976_0]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [hlam, p976_0]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [h767, hlam, p976_1]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [h745, hlam, p976_0]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [h4, h743, h745, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p976_1, u5ehi1]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [h766, hlam, p976_0]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [h4, h743, h745, h767, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p976_1, u3ehi3]
                                        · have p976_0 := h976c.1
                                          have p976_1 := h976c.2.1
                                          have p976_2 := h976c.2.2.1
                                          have p976_3 := h976c.2.2.2
                                          linarith only [hlam, p976_0]
                                      · linarith only [h975, hlam, p926_0]
                                    · linarith only [h600, h974, hlam]
                                  · linarith only [h4, h973, hlam]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              rcases p926_3 (m.d 0 2) (by simp) with h1023 | h1023
                              · linarith only [h1023, h713, hlam]
                              · linarith only [h0, h1023, hlam]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [h765, hlam, p926_1]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [h766, hlam, p926_0]
                            · have p926_0 := h926c.1
                              have p926_1 := h926c.2.1
                              have p926_2 := h926c.2.2.1
                              have p926_3 := h926c.2.2.2
                              linarith only [hlam, p926_0]
                          · rcases h2bigk with h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [hlam, p1029_0]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1029_1, p769_1]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [h4, hlam, p1029_0]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [h600, hlam, p1029_0]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [h713, hlam, p1029_0]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [h0, hlam, p1029_0]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [hlam, p1029_0]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [h746, hlam, p1029_0]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [h748, hlam, p1029_0]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [h750, hlam, p1029_0]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              rcases p1029_3 (m.d 0 2) (by simp) with h1040 | h1040
                              · linarith only [h1040, hlam, p1029_0]
                              · rcases p1029_3 (m.d 1 2) (by simp) with h1042 | h1042
                                · linarith only [h1042, h746, hlam]
                                · rcases p1029_3 (m.d 2 3) (by simp) with h1044 | h1044
                                  · rcases p1029_3 (m.d 2 4) (by simp) with h1045 | h1045
                                    · linarith only [h1045, h764, hlam]
                                    · linarith only [h1045, h600, hlam]
                                  · linarith only [h1044, hlam, p1029_0]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              rcases p1029_3 (m.d 0 2) (by simp) with h1049 | h1049
                              · linarith only [h1049, h4, hlam]
                              · linarith only [h0, h1049, hlam]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [hlam, p1029_0]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [h713, h766, hc02, hc23, hlam, hphi, p1029_1, p769_1]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [h0, h713, hc12, hc23, hlam, hphi, p1029_1, p769_1]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              rcases p1029_3 (m.d 0 2) (by simp) with h1055 | h1055
                              · linarith only [h1055, hlam, p1029_0]
                              · rcases p1029_3 (m.d 1 2) (by simp) with h1057 | h1057
                                · linarith only [h1057, h748, hlam]
                                · rcases p1029_3 (m.d 2 3) (by simp) with h1059 | h1059
                                  · rcases p1029_3 (m.d 2 4) (by simp) with h1060 | h1060
                                    · rcases p1029_3 (m.d 2 5) (by simp) with h1061 | h1061
                                      · linarith only [h1061, h766, hlam]
                                      · linarith only [h1061, h713, hlam]
                                    · linarith only [h1060, hlam, p1029_0]
                                  · linarith only [h1059, h4, hlam]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              rcases p1029_3 (m.d 0 2) (by simp) with h1066 | h1066
                              · linarith only [h1066, h600, hlam]
                              · linarith only [h0, h1066, hlam]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [h764, hlam, p1029_1]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [hlam, p1029_0]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [h0, h713, hc12, hc24, hlam, hphi, p1029_1, p769_1]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              rcases p1029_3 (m.d 0 2) (by simp) with h1072 | h1072
                              · linarith only [h1072, hlam, p1029_0]
                              · rcases p1029_3 (m.d 1 2) (by simp) with h1074 | h1074
                                · linarith only [h1074, h750, hlam]
                                · rcases p1029_3 (m.d 2 3) (by simp) with h1076 | h1076
                                  · rcases p1029_3 (m.d 2 4) (by simp) with h1077 | h1077
                                    · rcases p1029_3 (m.d 2 5) (by simp) with h1078 | h1078
                                      · rcases h5bigk with h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [hlam, p1079_0]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          rcases p1079_3 (m.d 0 5) (by simp) with h1081 | h1081
                                          · rcases p1079_3 (m.d 1 5) (by simp) with h1082 | h1082
                                            · linarith only [h1082, h3, hlam]
                                            · rcases p1079_3 (m.d 2 5) (by simp) with h1084 | h1084
                                              · rcases p1079_3 (m.d 3 5) (by simp) with h1085 | h1085
                                                · linarith only [h1085, h744, hlam]
                                                · rcases p1079_3 (m.d 4 5) (by simp) with h1087 | h1087
                                                  · linarith only [h1087, h745, hlam]
                                                  · linarith only [h1087, h754, hlam]
                                              · linarith only [h1084, h750, hlam]
                                          · linarith only [h1081, h3, hlam]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [h713, hlam, p1079_0]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          rcases p1079_3 (m.d 0 5) (by simp) with h1093 | h1093
                                          · rcases p1079_3 (m.d 1 5) (by simp) with h1094 | h1094
                                            · linarith only [h1094, h3, hlam]
                                            · linarith only [h1094, h753, hlam]
                                          · linarith only [h1093, h744, hlam]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [h600, h745, h752, h754, h764, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1079_1, u3ehi3]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [h3, hlam, p1079_0]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [hlam, p1079_0]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [h750, hlam, p1079_0]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [h3, h767, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1079_1, u3ehi3]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [h754, hlam, p1079_1]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [h0, hc12, hc25, hlam, hphi, p1079_1, p769_1]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          rcases p1079_3 (m.d 0 5) (by simp) with h1105 | h1105
                                          · linarith only [h1105, h713, hlam]
                                          · linarith only [h1105, h3, hlam]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [hlam, p1079_0]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          rcases p1079_3 (m.d 0 5) (by simp) with h1109 | h1109
                                          · linarith only [h1109, h713, hlam]
                                          · linarith only [h1109, h744, hlam]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [h752, h754, h764, h766, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1079_1, u3ehi3]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [h744, hlam, p1079_0]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [h753, hlam, p1079_0]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [h765, hlam, p1079_0]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [hlam, p1079_0]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [h767, hlam, p1079_1]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [h745, hlam, p1079_0]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [h600, h745, h764, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1079_1, u5ehi1]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [h766, hlam, p1079_0]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [h600, h745, h764, h767, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1079_1, u3ehi3]
                                        · have p1079_0 := h1079c.1
                                          have p1079_1 := h1079c.2.1
                                          have p1079_2 := h1079c.2.2.1
                                          have p1079_3 := h1079c.2.2.2
                                          linarith only [hlam, p1079_0]
                                      · linarith only [h1078, hlam, p1029_0]
                                    · linarith only [h1077, h600, hlam]
                                  · linarith only [h1076, h4, hlam]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              rcases p1029_3 (m.d 0 2) (by simp) with h1126 | h1126
                              · linarith only [h1126, h713, hlam]
                              · linarith only [h0, h1126, hlam]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [h765, hlam, p1029_1]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [h766, hlam, p1029_0]
                            · have p1029_0 := h1029c.1
                              have p1029_1 := h1029c.2.1
                              have p1029_2 := h1029c.2.2.1
                              have p1029_3 := h1029c.2.2.2
                              linarith only [hlam, p1029_0]
                          · rcases h2bigk with h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [hlam, p1132_0]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [h4, hc12, hc23, hlam, hphi, p1132_1]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [h4, hlam, p1132_0]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [h600, hlam, p1132_0]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [h713, hlam, p1132_0]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [h0, hlam, p1132_0]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [hlam, p1132_0]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [h746, hlam, p1132_0]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [h748, hlam, p1132_0]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [h750, hlam, p1132_0]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              rcases p1132_3 (m.d 0 2) (by simp) with h1143 | h1143
                              · linarith only [h1143, hlam, p1132_0]
                              · rcases p1132_3 (m.d 1 2) (by simp) with h1145 | h1145
                                · linarith only [h1145, h746, hlam]
                                · rcases p1132_3 (m.d 2 3) (by simp) with h1147 | h1147
                                  · rcases p1132_3 (m.d 2 4) (by simp) with h1148 | h1148
                                    · linarith only [h1148, h764, hlam]
                                    · linarith only [h1148, h600, hlam]
                                  · linarith only [h1147, hlam, p1132_0]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              rcases p1132_3 (m.d 0 2) (by simp) with h1152 | h1152
                              · linarith only [h1152, h4, hlam]
                              · linarith only [h0, h1152, hlam]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [hlam, p1132_0]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [h713, h766, hc02, hc23, hlam, hphi, p1132_1, p769_1]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [h713, h821, hc23, hlam, ht01, ht12, p1132_1]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              rcases p1132_3 (m.d 0 2) (by simp) with h1158 | h1158
                              · linarith only [h1158, hlam, p1132_0]
                              · rcases p1132_3 (m.d 1 2) (by simp) with h1160 | h1160
                                · linarith only [h1160, h748, hlam]
                                · rcases p1132_3 (m.d 2 3) (by simp) with h1162 | h1162
                                  · rcases p1132_3 (m.d 2 4) (by simp) with h1163 | h1163
                                    · rcases p1132_3 (m.d 2 5) (by simp) with h1164 | h1164
                                      · linarith only [h1164, h766, hlam]
                                      · linarith only [h1164, h713, hlam]
                                    · linarith only [h1163, hlam, p1132_0]
                                  · linarith only [h1162, h4, hlam]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              rcases p1132_3 (m.d 0 2) (by simp) with h1169 | h1169
                              · linarith only [h1169, h600, hlam]
                              · linarith only [h0, h1169, hlam]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [h764, hlam, p1132_1]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [hlam, p1132_0]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [h713, h821, hc24, hlam, ht01, ht12, p1132_1]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              rcases p1132_3 (m.d 0 2) (by simp) with h1175 | h1175
                              · linarith only [h1175, hlam, p1132_0]
                              · rcases p1132_3 (m.d 1 2) (by simp) with h1177 | h1177
                                · linarith only [h1177, h750, hlam]
                                · rcases p1132_3 (m.d 2 3) (by simp) with h1179 | h1179
                                  · rcases p1132_3 (m.d 2 4) (by simp) with h1180 | h1180
                                    · rcases p1132_3 (m.d 2 5) (by simp) with h1181 | h1181
                                      · rcases h5bigk with h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [hlam, p1182_0]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          rcases p1182_3 (m.d 0 5) (by simp) with h1184 | h1184
                                          · rcases p1182_3 (m.d 1 5) (by simp) with h1185 | h1185
                                            · linarith only [h1185, h3, hlam]
                                            · rcases p1182_3 (m.d 2 5) (by simp) with h1187 | h1187
                                              · rcases p1182_3 (m.d 3 5) (by simp) with h1188 | h1188
                                                · linarith only [h1188, h744, hlam]
                                                · rcases p1182_3 (m.d 4 5) (by simp) with h1190 | h1190
                                                  · linarith only [h1190, h745, hlam]
                                                  · linarith only [h1190, h754, hlam]
                                              · linarith only [h1187, h750, hlam]
                                          · linarith only [h1184, h3, hlam]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [h713, hlam, p1182_0]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          rcases p1182_3 (m.d 0 5) (by simp) with h1196 | h1196
                                          · rcases p1182_3 (m.d 1 5) (by simp) with h1197 | h1197
                                            · linarith only [h1197, h3, hlam]
                                            · linarith only [h1197, h753, hlam]
                                          · linarith only [h1196, h744, hlam]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [h743, h745, h752, h754, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1182_1, u3ehi3]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [h3, hlam, p1182_0]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [hlam, p1182_0]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [h750, hlam, p1182_0]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [h3, h767, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1182_1, u3ehi3]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [h754, hlam, p1182_1]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [h821, hc25, hlam, ht01, ht12, p1182_1]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          rcases p1182_3 (m.d 0 5) (by simp) with h1208 | h1208
                                          · linarith only [h1208, h713, hlam]
                                          · linarith only [h1208, h3, hlam]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [hlam, p1182_0]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          rcases p1182_3 (m.d 0 5) (by simp) with h1212 | h1212
                                          · linarith only [h1212, h713, hlam]
                                          · linarith only [h1212, h744, hlam]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [h752, h754, h764, h766, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1182_1, u3ehi3]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [h744, hlam, p1182_0]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [h753, hlam, p1182_0]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [h765, hlam, p1182_0]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [hlam, p1182_0]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [h767, hlam, p1182_1]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [h745, hlam, p1182_0]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [h4, h743, h745, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1182_1, u5ehi1]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [h766, hlam, p1182_0]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [h4, h743, h745, h767, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1182_1, u3ehi3]
                                        · have p1182_0 := h1182c.1
                                          have p1182_1 := h1182c.2.1
                                          have p1182_2 := h1182c.2.2.1
                                          have p1182_3 := h1182c.2.2.2
                                          linarith only [hlam, p1182_0]
                                      · linarith only [h1181, hlam, p1132_0]
                                    · linarith only [h1180, h600, hlam]
                                  · linarith only [h1179, h4, hlam]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              rcases p1132_3 (m.d 0 2) (by simp) with h1229 | h1229
                              · linarith only [h1229, h713, hlam]
                              · linarith only [h0, h1229, hlam]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [h765, hlam, p1132_1]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [h766, hlam, p1132_0]
                            · have p1132_0 := h1132c.1
                              have p1132_1 := h1132c.2.1
                              have p1132_2 := h1132c.2.2.1
                              have p1132_3 := h1132c.2.2.2
                              linarith only [hlam, p1132_0]
                        · linarith only [h713, h820, hlam]
                      · linarith only [h600, h819, hlam]
                    · linarith only [h4, h818, hlam]
                · linarith only [h0, h815, hlam]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [h744, hlam, p769_0]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [h745, hlam, p769_1]
              · have p769_0 := h769c.1
                have p769_1 := h769c.2.1
                have p769_2 := h769c.2.2.1
                have p769_3 := h769c.2.2.2
                linarith only [hlam, p769_0]
          · linarith only [h0, h4, h600, h743, h745, h766, hc12, hc23, hlam, hphi]
        · linarith only [h4, h743, h765, hc35, hlam, hphi, u3ehi3]
      · linarith only [h4, h743, h745, h752, h754, h764, hlam]
  · linarith only [h752, h753, hc35, hlam, hphi, u3ehi3]

end R2N4
