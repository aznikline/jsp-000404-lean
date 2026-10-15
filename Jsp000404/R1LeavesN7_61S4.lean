import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3258000 in
set_option maxHeartbeats 3258000 in
theorem r1l7_10_12_13_25_L_R_L_R_L_I_H_I_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h752 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h753 | h753
  · rcases m.htr 0 2 3 (by decide) (by decide) with h754 | h754
    · rcases m.htr 0 2 4 (by decide) (by decide) with h755 | h755
      · rcases m.htr 0 2 5 (by decide) (by decide) with h756 | h756
        · rcases m.htr 0 3 5 (by decide) (by decide) with h757 | h757
          · rcases m.htr 0 4 5 (by decide) (by decide) with h758 | h758
            · rcases m.htr 1 2 3 (by decide) (by decide) with h759 | h759
              · rcases m.htr 1 2 4 (by decide) (by decide) with h760 | h760
                · rcases m.htr 1 2 5 (by decide) (by decide) with h761 | h761
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h762 | h762
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h763 | h763
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h764 | h764
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h765 | h765
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h766 | h766
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h767 | h767
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h768 | h768
                                · linarith only [h0, h752, h759, h765, h768, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h0, h752, h762, h764, h768, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h752, h762, h764, h767, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h752, h757, h766, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h0, h752, h762, h765, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h774 | h774
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h775 | h775
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h776 | h776
                              · linarith only [h0, h752, h759, h764, h774, h776, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h778 | h778
                                · linarith only [h0, h752, h759, h760, h764, h774, h778, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · rcases h5bigk with h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [hlam, p780_0]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h0, h752, h757, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p780_1]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h0, h752, h757, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p780_1, u2ehi4]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h0, h752, h757, h778, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p780_1]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h0, h752, h757, h760, h764, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p780_1, u2ehi3]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h753, hlam, p780_0]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [hlam, p780_0]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p780_1, u2ehi4]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h0, h752, h763, h778, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p780_1]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h764, hlam, p780_1]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h756, hlam, p780_1]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h761, hlam, p780_1]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [hlam, p780_0]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h0, h756, h778, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p780_1]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h776, hlam, p780_1]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h757, hlam, p780_0]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h763, hlam, p780_0]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h775, hlam, p780_0]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [hlam, p780_0]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h778, hlam, p780_1]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h758, hlam, p780_0]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h761, hc45, hlam, hphi, ht23, ht34, p780_1, u2ehi4]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h0, h752, h757, h758, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p780_1, u2ehi4]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [h0, h752, h757, h758, h778, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p780_1]
                                  · have p780_0 := h780c.1
                                    have p780_1 := h780c.2.1
                                    have p780_2 := h780c.2.2.1
                                    have p780_3 := h780c.2.2.2
                                    linarith only [hlam, p780_0]
                            · linarith only [h0, h752, h757, h775, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h0, h752, h762, h774, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h752, h757, h762, h763, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h809 | h809
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h810 | h810
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h811 | h811
                          · linarith only [h761, h762, h809, h811, hc23, hlam, hphi, u2ehi4]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h813 | h813
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h814 | h814
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h815 | h815
                                · rcases h5bigk with h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [hlam, p816_0]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h0, h752, h757, h761, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p816_1, u2ehi4]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h0, h752, h757, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p816_1, u2ehi4]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h0, h752, h757, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p816_1]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h0, h752, h757, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p816_1]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h753, hlam, p816_0]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [hlam, p816_0]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h809, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p816_1, u2ehi4]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h0, h752, h809, h815, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p816_1]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h0, h752, h809, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p816_1]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h756, hlam, p816_1]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h761, hlam, p816_1]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [hlam, p816_0]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h0, h752, h761, h809, h815, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p816_1]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h0, h752, h761, h809, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p816_1]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h757, hlam, p816_0]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h809, hlam, p816_0]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h813, hlam, p816_0]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [hlam, p816_0]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h0, h752, h757, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p816_1]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h758, hlam, p816_0]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h810, hlam, p816_0]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h814, hlam, p816_0]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [h815, hlam, p816_0]
                                  · have p816_0 := h816c.1
                                    have p816_1 := h816c.2.1
                                    have p816_2 := h816c.2.2.1
                                    have p816_3 := h816c.2.2.2
                                    linarith only [hlam, p816_0]
                                · linarith only [h0, h752, h757, h758, h761, h762, h809, h815, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                              · linarith only [h762, h809, h810, h814, hc34, hlam, hphi, ht23, u2ehi3]
                            · linarith only [h0, h752, h809, h813, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h762, h809, h810, hlam]
                      · linarith only [h0, h752, h757, h759, h809, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h761, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h0, h752, h759, h760, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h759, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h850 | h850
              · rcases m.htr 1 2 4 (by decide) (by decide) with h851 | h851
                · rcases m.htr 1 2 5 (by decide) (by decide) with h852 | h852
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h853 | h853
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h854 | h854
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h855 | h855
                        · linarith only [h0, h752, h758, h853, h855, hc12, hlam, hphi, ht01, u0ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h857 | h857
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h858 | h858
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h859 | h859
                              · linarith only [h0, h752, h758, h851, h854, h855, h859, hc12, hlam, hphi, ht01, u0ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h861 | h861
                                · linarith only [h0, h752, h758, h850, h857, h861, hc12, hlam, hphi, ht01, u0ehi3]
                                · rcases h5bigk with h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [hlam, p863_0]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h757, h851, h855, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p863_1, u2ehi3]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h0, h752, h757, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p863_1]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h0, h752, h757, h861, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p863_1]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h758, hlam, p863_1]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h753, hlam, p863_0]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [hlam, p863_0]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h0, h753, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p863_1, u2ehi4]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h0, h752, h854, h861, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p863_1]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h855, hlam, p863_1]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h756, hlam, p863_1]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h852, hlam, p863_1]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [hlam, p863_0]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h0, h756, h861, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p863_1]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h859, hlam, p863_1]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h757, hlam, p863_0]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h854, hlam, p863_0]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h858, hlam, p863_0]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [hlam, p863_0]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h861, hlam, p863_1]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p863_1, u0ehi4]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h851, h855, hc45, hlam, hphi, ht23, ht34, p863_1, u2ehi3]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht23, ht34, p863_1, u2ehi4]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [h861, hc34, hc45, hlam, hphi, p863_1]
                                  · have p863_0 := h863c.1
                                    have p863_1 := h863c.2.1
                                    have p863_2 := h863c.2.2.1
                                    have p863_3 := h863c.2.2.2
                                    linarith only [hlam, p863_0]
                            · linarith only [h0, h752, h757, h858, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h0, h752, h853, h857, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h752, h757, h853, h854, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h892 | h892
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h893 | h893
                        · linarith only [h758, h893, hc14, hlam, hphi, ht01, u0ehi3]
                        · linarith only [h853, h892, h893, hlam]
                      · linarith only [h0, h752, h757, h850, h892, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h852, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h0, h752, h850, h851, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h850, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h900 | h900
            · rcases m.htr 1 2 3 (by decide) (by decide) with h901 | h901
              · rcases m.htr 1 2 4 (by decide) (by decide) with h902 | h902
                · rcases m.htr 1 2 5 (by decide) (by decide) with h903 | h903
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h904 | h904
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h905 | h905
                      · linarith only [h752, h757, h905, hc01, hlam, hphi, u0ehi2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h907 | h907
                        · linarith only [h904, h905, h907, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h909 | h909
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h910 | h910
                            · linarith only [h757, h910, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h912 | h912
                              · linarith only [h902, h907, h912, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h914 | h914
                                · linarith only [h0, h753, h901, h902, h905, h907, h909, h914, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h757, h900, h914, hc04, hlam, hphi, u0ehi2]
                          · linarith only [h0, h753, h904, h905, h909, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h918 | h918
                      · linarith only [h757, h918, hc13, hlam, hphi, ht01, u0ehi2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h920 | h920
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h921 | h921
                          · linarith only [h0, h753, h901, h902, h904, h918, h921, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h923 | h923
                            · linarith only [h757, h923, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h925 | h925
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h926 | h926
                                · rcases h5bigk with h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [hlam, p927_0]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [h0, h753, h901, h918, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p927_1, u2ehi2]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [h0, h753, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p927_1]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [h757, hlam, p927_1]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [h0, h753, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p927_1]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [h753, hlam, p927_0]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [hlam, p927_0]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [h920, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p927_1, u2ehi4]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [h918, hlam, p927_1]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [h0, h753, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p927_1]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [h756, hlam, p927_1]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [h903, hlam, p927_1]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [hlam, p927_0]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [h923, hlam, p927_1]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [h0, h756, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p927_1]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p927_1, u0ehi4]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [h903, hc35, hlam, hphi, ht23, p927_1, u2ehi4]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [hc35, hlam, hphi, ht23, p927_1, u2ehi4]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [hlam, p927_0]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    rcases p927_3 (m.d 0 5) (by simp) with h947 | h947
                                    · linarith only [h757, h947, hlam]
                                    · linarith only [h900, h947, hlam]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [h900, hlam, p927_0]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [h920, hlam, p927_0]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [h925, hlam, p927_0]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [h926, hlam, p927_0]
                                  · have p927_0 := h927c.1
                                    have p927_1 := h927c.2.1
                                    have p927_2 := h927c.2.2.1
                                    have p927_3 := h927c.2.2.2
                                    linarith only [hlam, p927_0]
                                · linarith only [h0, h755, h900, h901, h904, h926, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h904, h920, h925, hc34, hlam, hphi, ht23, u2ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h957 | h957
                          · linarith only [h901, h904, h957, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h959 | h959
                            · linarith only [h757, h900, h901, h904, h920, h959, hc05, hlam, hphi, u0ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h961 | h961
                              · linarith only [h902, h920, h961, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h963 | h963
                                · linarith only [h902, h920, h957, h963, hc34, hlam, hphi, ht23, u2ehi2]
                                · linarith only [h0, h753, h900, h901, h904, h963, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h903, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h0, h752, h901, h902, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h901, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h969 | h969
              · rcases m.htr 1 2 4 (by decide) (by decide) with h970 | h970
                · rcases m.htr 1 2 5 (by decide) (by decide) with h971 | h971
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h972 | h972
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h973 | h973
                      · linarith only [h752, h757, h973, hc01, hlam, hphi, u0ehi2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h975 | h975
                        · linarith only [h0, h753, h900, h972, h973, h975, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h977 | h977
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h978 | h978
                            · linarith only [h757, h978, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h980 | h980
                              · linarith only [h0, h753, h900, h970, h972, h973, h980, hc12, hlam, hphi, ht01, u0ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h982 | h982
                                · linarith only [h0, h753, h900, h969, h973, h977, h982, hc12, hlam, hphi, ht01, u0ehi3]
                                · rcases h5bigk with h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c | h984c
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [hlam, p984_0]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h970, h972, h973, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p984_1, u2ehi3]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h0, h753, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p984_1]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h757, hlam, p984_1]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h900, hlam, p984_1]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h753, hlam, p984_0]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [hlam, p984_0]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h0, h753, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p984_1, u2ehi4]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h973, hlam, p984_1]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h975, hlam, p984_1]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h756, hlam, p984_1]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h971, hlam, p984_1]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [hlam, p984_0]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h978, hlam, p984_1]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h980, hlam, p984_1]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h982, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p984_1, u0ehi4]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h970, h972, h973, h982, hc45, hlam, hphi, ht23, ht34, p984_1, u2ehi3]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h982, hc45, hlam, hphi, ht23, ht34, p984_1, u2ehi4]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [hlam, p984_0]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h982, hlam, p984_1]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h0, h753, h757, h970, h972, h973, hc12, hc45, hlam, hphi, ht01, ht23, ht34, p984_1, u0ehi2, u2ehi3]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h970, h972, h973, hc45, hlam, hphi, ht23, ht34, p984_1, u2ehi3]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h977, h978, hc45, hlam, hphi, ht23, ht34, p984_1, u2ehi3]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [h0, h753, h757, h970, h972, h973, hc12, hc45, hlam, hphi, ht01, ht23, ht34, p984_1, u0ehi2, u2ehi3]
                                  · have p984_0 := h984c.1
                                    have p984_1 := h984c.2.1
                                    have p984_2 := h984c.2.2.1
                                    have p984_3 := h984c.2.2.2
                                    linarith only [hlam, p984_0]
                          · linarith only [h0, h753, h972, h973, h977, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1011 | h1011
                      · linarith only [h1011, h757, hc13, hlam, hphi, ht01, u0ehi2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1013 | h1013
                        · linarith only [h0, h1011, h1013, h753, h900, h969, h972, hc12, hc34, hlam, hphi, ht01, ht23, u0ehi3, u2ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1015 | h1015
                          · linarith only [h1015, h969, h972, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1017 | h1017
                            · linarith only [h0, h1013, h1017, h753, h757, h969, h972, hc12, hlam, hphi, ht01, u0ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1019 | h1019
                              · linarith only [h0, h1013, h1019, h753, h900, h970, hc12, hlam, hphi, ht01, u0ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1021 | h1021
                                · linarith only [h0, h1013, h1021, h753, h900, h969, h972, hc12, hc34, hlam, hphi, ht01, ht23, u0ehi3, u2ehi2]
                                · linarith only [h1021, h969, h972, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h971, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h0, h752, h755, h969, h970, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h0, h969, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h754, h756, hc25, hlam, hphi, u2ehi2]
      · linarith only [h754, h755, hc24, hlam, hphi, u2ehi2]
    · linarith only [h0, h752, h754, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1030 | h1030
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1031 | h1031
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1032 | h1032
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1033 | h1033
          · linarith only [h1033, h752, h753, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1035 | h1035
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1036 | h1036
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1037 | h1037
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1038 | h1038
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1039 | h1039
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1040 | h1040
                      · linarith only [h1033, h1040, h752, hc01, hlam, hphi, u0ehi2]
                      · linarith only [h1037, h1039, h1040, h752, h753, hc35, hlam, hphi, ht23, u2ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1043 | h1043
                      · linarith only [h1033, h1038, h1043, h752, h753, hc12, hlam, hphi, ht01, u0ehi2]
                      · linarith only [h1036, h1043, h752, h753, hc35, hlam, hphi, ht23, u2ehi2]
                  · linarith only [h0, h1032, h1036, h1038, h752, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h1032, h1037, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h1036, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1049 | h1049
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1050 | h1050
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1051 | h1051
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1052 | h1052
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1053 | h1053
                      · linarith only [h1033, h1051, h1053, h752, h753, hc12, hlam, hphi, ht01, u0ehi2]
                      · linarith only [h1050, h1052, h1053, h752, h753, hc35, hlam, hphi, ht23, u2ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1056 | h1056
                      · linarith only [h1033, h1051, h1056, h752, h753, hc12, hlam, hphi, ht01, u0ehi2]
                      · linarith only [h1049, h1056, h752, h753, hc35, hlam, hphi, ht23, u2ehi2]
                  · linarith only [h0, h1049, h1051, h752, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h1049, h1050, h752, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h1049, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h1031, h1032, hc25, hlam, hphi, u2ehi3]
      · linarith only [h1030, h1031, hc24, hlam, hphi, u2ehi2]
    · linarith only [h0, h1030, h752, hlam]

end R2N4
