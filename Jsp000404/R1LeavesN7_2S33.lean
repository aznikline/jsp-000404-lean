import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h22729 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h22730 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h22731 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h22732 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h22733 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h22734 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  rcases m.htr 2 3 4 (by decide) (by decide) with h22735 | h22735
  · rcases m.htr 2 3 5 (by decide) (by decide) with h22736 | h22736
    · rcases m.htr 2 4 5 (by decide) (by decide) with h22737 | h22737
      · linarith only [h20409, h20413, h22737, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h22739 | h22739
        · linarith only [h20409, h20413, h22735, h22739, hlam]
        · rcases h0bigk with h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c | h22741c
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [hlam, p22741_0]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [h0, hlam, p22741_1]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [h14396, hlam, p22741_0]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [h16915, hlam, p22741_1]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [h18815, hlam, p22741_1]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            rcases p22741_3 (m.d 0 1) (by simp) with h22747 | h22747
            · linarith only [h0, h22747, hlam]
            · rcases p22741_3 (m.d 0 2) (by simp) with h22749 | h22749
              · rcases p22741_3 (m.d 0 3) (by simp) with h22750 | h22750
                · linarith only [h20408, h22750, hlam]
                · linarith only [h14396, h22750, hlam]
              · linarith only [h0, h22749, hlam]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [hlam, p22741_0]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            rcases p22741_3 (m.d 0 1) (by simp) with h22755 | h22755
            · linarith only [h0, h22755, hlam]
            · rcases p22741_3 (m.d 0 2) (by simp) with h22757 | h22757
              · rcases p22741_3 (m.d 0 3) (by simp) with h22758 | h22758
                · linarith only [h20408, h22758, hlam]
                · rcases p22741_3 (m.d 0 4) (by simp) with h22760 | h22760
                  · linarith only [h20409, h22760, hlam]
                  · rcases p22741_3 (m.d 0 5) (by simp) with h22762 | h22762
                    · linarith only [h20410, h22762, hlam]
                    · rcases h2bigk with h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c | h22764c
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [hlam, p22764_0]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [h0, hlam, p22764_1]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        rcases p22764_3 (m.d 0 2) (by simp) with h22767 | h22767
                        · rcases p22764_3 (m.d 1 2) (by simp) with h22768 | h22768
                          · rcases p22764_3 (m.d 2 3) (by simp) with h22769 | h22769
                            · linarith only [h22769, hlam, p22764_0]
                            · rcases p22764_3 (m.d 2 4) (by simp) with h22771 | h22771
                              · linarith only [h20409, h22771, hlam]
                              · rcases p22764_3 (m.d 2 5) (by simp) with h22773 | h22773
                                · linarith only [h20410, h22773, hlam]
                                · rcases h3bigk with h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c | h22775c
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [hlam, p22775_0]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h14396, hlam, p22775_1]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h22736, h22739, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p22741_1, p22775_1]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22741_1, p22775_1]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h0, h22739, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22741_1, p22775_1]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h16915, h20412, h20413, h22729, hc01, hc12, hlam, hphi, p22775_1]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [hlam, p22775_0]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h22729, h22736, h22739, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22775_1]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    rcases p22775_3 (m.d 0 3) (by simp) with h22784 | h22784
                                    · linarith only [h14396, h22784, hlam]
                                    · linarith only [h20411, h22784, hlam]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    rcases p22775_3 (m.d 0 3) (by simp) with h22787 | h22787
                                    · linarith only [h14396, h22787, hlam]
                                    · linarith only [h20412, h22787, hlam]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h20408, hlam, p22775_0]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h22729, hlam, p22775_0]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [hlam, p22775_0]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h20408, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p22741_1, p22775_1]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h0, h20408, h22739, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22741_1, p22775_1]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h20411, hlam, p22775_0]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h22732, hlam, p22775_0]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h22735, hlam, p22775_0]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [hlam, p22775_0]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h22739, hlam, p22775_1]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h20412, hlam, p22775_0]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h22733, hlam, p22775_0]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h22736, hlam, p22775_0]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [h0, h20412, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22741_1, p22775_1]
                                  · have p22775_0 := h22775c.1
                                    have p22775_1 := h22775c.2.1
                                    have p22775_2 := h22775c.2.2.1
                                    have p22775_3 := h22775c.2.2.2
                                    linarith only [hlam, p22775_0]
                          · linarith only [h22729, h22768, hlam]
                        · linarith only [h22767, hlam, p22764_0]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        rcases p22764_3 (m.d 0 2) (by simp) with h22807 | h22807
                        · rcases p22764_3 (m.d 1 2) (by simp) with h22808 | h22808
                          · rcases p22764_3 (m.d 2 3) (by simp) with h22809 | h22809
                            · linarith only [h20408, h22809, hlam]
                            · linarith only [h22735, h22809, hlam]
                          · linarith only [h22730, h22808, hlam]
                        · linarith only [h22807, hlam, p22764_0]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        rcases p22764_3 (m.d 0 2) (by simp) with h22814 | h22814
                        · rcases p22764_3 (m.d 1 2) (by simp) with h22815 | h22815
                          · rcases p22764_3 (m.d 2 3) (by simp) with h22816 | h22816
                            · linarith only [h20408, h22816, hlam]
                            · linarith only [h22736, h22816, hlam]
                          · linarith only [h22731, h22815, hlam]
                        · linarith only [h22814, hlam, p22764_0]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22741_1, p22764_1]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [hlam, p22764_0]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        rcases p22764_3 (m.d 0 2) (by simp) with h22823 | h22823
                        · linarith only [h0, h22823, hlam]
                        · linarith only [h20408, h22823, hlam]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        rcases p22764_3 (m.d 0 2) (by simp) with h22826 | h22826
                        · linarith only [h0, h22826, hlam]
                        · linarith only [h20409, h22826, hlam]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        rcases p22764_3 (m.d 0 2) (by simp) with h22829 | h22829
                        · linarith only [h0, h22829, hlam]
                        · linarith only [h20410, h22829, hlam]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [h20408, hlam, p22764_0]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [h22729, hlam, p22764_0]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [hlam, p22764_0]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [h20408, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p22741_1, p22764_1]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [h0, h20408, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p22741_1, p22764_1]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [h20409, hlam, p22764_0]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [h22730, hlam, p22764_0]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [h22735, hlam, p22764_1]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [hlam, p22764_0]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [h22737, hlam, p22764_1]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [h20410, hlam, p22764_0]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [h22731, hlam, p22764_0]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [h22736, hlam, p22764_1]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [h0, h20410, h20412, h22735, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22741_1, p22764_1]
                      · have p22764_0 := h22764c.1
                        have p22764_1 := h22764c.2.1
                        have p22764_2 := h22764c.2.2.1
                        have p22764_3 := h22764c.2.2.2
                        linarith only [hlam, p22764_0]
              · linarith only [h20408, h22757, hlam]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            rcases p22741_3 (m.d 0 1) (by simp) with h22848 | h22848
            · linarith only [h0, h22848, hlam]
            · rcases p22741_3 (m.d 0 2) (by simp) with h22850 | h22850
              · rcases p22741_3 (m.d 0 3) (by simp) with h22851 | h22851
                · linarith only [h20408, h22851, hlam]
                · linarith only [h20411, h22851, hlam]
              · linarith only [h20409, h22850, hlam]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            rcases p22741_3 (m.d 0 1) (by simp) with h22855 | h22855
            · linarith only [h0, h22855, hlam]
            · rcases p22741_3 (m.d 0 2) (by simp) with h22857 | h22857
              · rcases p22741_3 (m.d 0 3) (by simp) with h22858 | h22858
                · linarith only [h20408, h22858, hlam]
                · linarith only [h20412, h22858, hlam]
              · linarith only [h20410, h22857, hlam]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            rcases p22741_3 (m.d 0 1) (by simp) with h22862 | h22862
            · linarith only [h14396, h22862, hlam]
            · rcases p22741_3 (m.d 0 2) (by simp) with h22864 | h22864
              · rcases p22741_3 (m.d 0 3) (by simp) with h22865 | h22865
                · rcases p22741_3 (m.d 0 4) (by simp) with h22866 | h22866
                  · linarith only [h20411, h22866, hlam]
                  · linarith only [h16915, h22866, hlam]
                · linarith only [h14396, h22865, hlam]
              · linarith only [h0, h22864, hlam]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [h20408, hlam, p22741_1]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [hlam, p22741_0]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            rcases p22741_3 (m.d 0 1) (by simp) with h22873 | h22873
            · linarith only [h14396, h22873, hlam]
            · rcases p22741_3 (m.d 0 2) (by simp) with h22875 | h22875
              · rcases p22741_3 (m.d 0 3) (by simp) with h22876 | h22876
                · rcases p22741_3 (m.d 0 4) (by simp) with h22877 | h22877
                  · linarith only [h20411, h22877, hlam]
                  · rcases p22741_3 (m.d 0 5) (by simp) with h22879 | h22879
                    · linarith only [h20412, h22879, hlam]
                    · linarith only [h20413, h22879, hlam]
                · linarith only [h20411, h22876, hlam]
              · linarith only [h20409, h22875, hlam]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            rcases p22741_3 (m.d 0 1) (by simp) with h22884 | h22884
            · linarith only [h14396, h22884, hlam]
            · rcases p22741_3 (m.d 0 2) (by simp) with h22886 | h22886
              · rcases p22741_3 (m.d 0 3) (by simp) with h22887 | h22887
                · rcases p22741_3 (m.d 0 4) (by simp) with h22888 | h22888
                  · linarith only [h20411, h22888, hlam]
                  · rcases p22741_3 (m.d 0 5) (by simp) with h22890 | h22890
                    · linarith only [h20412, h22890, hlam]
                    · rcases h2bigk with h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c | h22892c
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        linarith only [hlam, p22892_0]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        linarith only [h0, hlam, p22892_1]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        rcases p22892_3 (m.d 0 2) (by simp) with h22895 | h22895
                        · rcases p22892_3 (m.d 1 2) (by simp) with h22896 | h22896
                          · rcases p22892_3 (m.d 2 3) (by simp) with h22897 | h22897
                            · linarith only [h22897, hlam, p22892_0]
                            · rcases p22892_3 (m.d 2 4) (by simp) with h22899 | h22899
                              · linarith only [h20409, h22899, hlam]
                              · rcases p22892_3 (m.d 2 5) (by simp) with h22901 | h22901
                                · linarith only [h20410, h22901, hlam]
                                · rcases h3bigk with h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c | h22903c
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [hlam, p22903_0]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [h14396, hlam, p22903_1]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [h20408, hlam, p22892_2, p22903_1]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    rcases p22903_3 (m.d 0 3) (by simp) with h22907 | h22907
                                    · rcases p22903_3 (m.d 1 3) (by simp) with h22908 | h22908
                                      · rcases p22903_3 (m.d 2 3) (by simp) with h22909 | h22909
                                        · linarith only [h20408, h22909, hlam]
                                        · linarith only [h22735, h22909, hlam]
                                      · linarith only [h22732, h22908, hlam]
                                    · linarith only [h22907, hlam, p22903_0]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    rcases p22903_3 (m.d 0 3) (by simp) with h22914 | h22914
                                    · rcases p22903_3 (m.d 1 3) (by simp) with h22915 | h22915
                                      · rcases p22903_3 (m.d 2 3) (by simp) with h22916 | h22916
                                        · linarith only [h20408, h22916, hlam]
                                        · linarith only [h22736, h22916, hlam]
                                      · linarith only [h22733, h22915, hlam]
                                    · linarith only [h22914, hlam, p22903_0]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [h22729, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p22741_1, p22903_1]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [hlam, p22903_0]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [h22729, h22736, h22739, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22903_1]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    rcases p22903_3 (m.d 0 3) (by simp) with h22924 | h22924
                                    · linarith only [h14396, h22924, hlam]
                                    · linarith only [h20411, h22924, hlam]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    rcases p22903_3 (m.d 0 3) (by simp) with h22927 | h22927
                                    · linarith only [h14396, h22927, hlam]
                                    · linarith only [h20412, h22927, hlam]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [h20408, hlam, p22903_0]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [h22729, hlam, p22903_0]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [hlam, p22903_0]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p22892_1, p22903_1]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [h0, h22739, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22892_1, p22903_1]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [h20411, hlam, p22903_0]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [h22732, hlam, p22903_0]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [h22735, hlam, p22903_0]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [hlam, p22903_0]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [h22739, hlam, p22903_1]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [h20412, hlam, p22903_0]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [h22733, hlam, p22903_0]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [h22736, hlam, p22903_0]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [h20412, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p22903_1]
                                  · have p22903_0 := h22903c.1
                                    have p22903_1 := h22903c.2.1
                                    have p22903_2 := h22903c.2.2.1
                                    have p22903_3 := h22903c.2.2.2
                                    linarith only [hlam, p22903_0]
                          · linarith only [h22729, h22896, hlam]
                        · linarith only [h22895, hlam, p22892_0]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        rcases p22892_3 (m.d 0 2) (by simp) with h22947 | h22947
                        · rcases p22892_3 (m.d 1 2) (by simp) with h22948 | h22948
                          · rcases p22892_3 (m.d 2 3) (by simp) with h22949 | h22949
                            · linarith only [h20408, h22949, hlam]
                            · linarith only [h22735, h22949, hlam]
                          · linarith only [h22730, h22948, hlam]
                        · linarith only [h22947, hlam, p22892_0]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        rcases p22892_3 (m.d 0 2) (by simp) with h22954 | h22954
                        · rcases p22892_3 (m.d 1 2) (by simp) with h22955 | h22955
                          · rcases p22892_3 (m.d 2 3) (by simp) with h22956 | h22956
                            · linarith only [h20408, h22956, hlam]
                            · linarith only [h22736, h22956, hlam]
                          · linarith only [h22731, h22955, hlam]
                        · linarith only [h22954, hlam, p22892_0]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        linarith only [h20408, h22736, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p22892_1]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        linarith only [hlam, p22892_0]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        rcases p22892_3 (m.d 0 2) (by simp) with h22963 | h22963
                        · linarith only [h0, h22963, hlam]
                        · linarith only [h20408, h22963, hlam]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        rcases p22892_3 (m.d 0 2) (by simp) with h22966 | h22966
                        · linarith only [h0, h22966, hlam]
                        · linarith only [h20409, h22966, hlam]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        rcases p22892_3 (m.d 0 2) (by simp) with h22969 | h22969
                        · linarith only [h0, h22969, hlam]
                        · linarith only [h20410, h22969, hlam]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        linarith only [h20408, hlam, p22892_0]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        linarith only [h22729, hlam, p22892_0]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        linarith only [hlam, p22892_0]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        rcases p22892_3 (m.d 0 2) (by simp) with h22975 | h22975
                        · rcases p22892_3 (m.d 1 2) (by simp) with h22976 | h22976
                          · rcases p22892_3 (m.d 2 3) (by simp) with h22977 | h22977
                            · rcases p22892_3 (m.d 2 4) (by simp) with h22978 | h22978
                              · linarith only [h22735, h22978, hlam]
                              · rcases p22892_3 (m.d 2 5) (by simp) with h22980 | h22980
                                · linarith only [h22736, h22980, hlam]
                                · linarith only [h22737, h22980, hlam]
                            · linarith only [h22735, h22977, hlam]
                          · linarith only [h22730, h22976, hlam]
                        · linarith only [h20409, h22975, hlam]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        rcases p22892_3 (m.d 0 2) (by simp) with h22986 | h22986
                        · rcases p22892_3 (m.d 1 2) (by simp) with h22987 | h22987
                          · rcases p22892_3 (m.d 2 3) (by simp) with h22988 | h22988
                            · rcases p22892_3 (m.d 2 4) (by simp) with h22989 | h22989
                              · linarith only [h22735, h22989, hlam]
                              · rcases p22892_3 (m.d 2 5) (by simp) with h22991 | h22991
                                · linarith only [h22736, h22991, hlam]
                                · rcases h3bigk with h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c | h22993c
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [hlam, p22993_0]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [h14396, hlam, p22993_1]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [h22737, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p22892_1, p22993_1]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    rcases p22993_3 (m.d 0 3) (by simp) with h22997 | h22997
                                    · rcases p22993_3 (m.d 1 3) (by simp) with h22998 | h22998
                                      · rcases p22993_3 (m.d 2 3) (by simp) with h22999 | h22999
                                        · linarith only [h20408, h22999, hlam]
                                        · linarith only [h22735, h22999, hlam]
                                      · linarith only [h22732, h22998, hlam]
                                    · linarith only [h22997, hlam, p22993_0]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    rcases p22993_3 (m.d 0 3) (by simp) with h23004 | h23004
                                    · rcases p22993_3 (m.d 1 3) (by simp) with h23005 | h23005
                                      · rcases p22993_3 (m.d 2 3) (by simp) with h23006 | h23006
                                        · linarith only [h20408, h23006, hlam]
                                        · linarith only [h22736, h23006, hlam]
                                      · linarith only [h22733, h23005, hlam]
                                    · linarith only [h23004, hlam, p22993_0]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [h14396, h22729, hc01, hc12, hlam, hphi, p22993_1]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [hlam, p22993_0]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [h22729, h22735, h22737, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22892_1, p22993_1]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    rcases p22993_3 (m.d 0 3) (by simp) with h23014 | h23014
                                    · linarith only [h14396, h23014, hlam]
                                    · linarith only [h20411, h23014, hlam]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    rcases p22993_3 (m.d 0 3) (by simp) with h23017 | h23017
                                    · linarith only [h14396, h23017, hlam]
                                    · linarith only [h20412, h23017, hlam]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [h20408, hlam, p22993_0]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [h22729, hlam, p22993_0]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [hlam, p22993_0]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [h0, h20408, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22993_1]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [h0, h20408, h22739, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22993_1]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [h20411, hlam, p22993_0]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [h22732, hlam, p22993_0]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [h22735, hlam, p22993_0]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [hlam, p22993_0]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [h22739, hlam, p22993_1]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [h20412, hlam, p22993_0]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [h22733, hlam, p22993_0]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [h22736, hlam, p22993_0]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [h20412, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p22993_1]
                                  · have p22993_0 := h22993c.1
                                    have p22993_1 := h22993c.2.1
                                    have p22993_2 := h22993c.2.2.1
                                    have p22993_3 := h22993c.2.2.2
                                    linarith only [hlam, p22993_0]
                            · linarith only [h22736, h22988, hlam]
                          · linarith only [h22731, h22987, hlam]
                        · linarith only [h20410, h22986, hlam]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        linarith only [h20409, hlam, p22892_0]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        linarith only [h22730, hlam, p22892_0]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        linarith only [h22735, hlam, p22892_1]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        linarith only [hlam, p22892_0]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        linarith only [h22737, hlam, p22892_1]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        linarith only [h20410, hlam, p22892_0]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        linarith only [h22731, hlam, p22892_0]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        linarith only [h22736, hlam, p22892_1]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        linarith only [h14396, h20410, h22729, h22735, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22741_1, p22892_1]
                      · have p22892_0 := h22892c.1
                        have p22892_1 := h22892c.2.1
                        have p22892_2 := h22892c.2.2.1
                        have p22892_3 := h22892c.2.2.2
                        linarith only [hlam, p22892_0]
                · linarith only [h20412, h22887, hlam]
              · linarith only [h20410, h22886, hlam]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [h20413, h22729, h22732, h22734, hc01, hc12, hlam, hphi, p22741_1]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [h20409, hlam, p22741_0]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [h20411, hlam, p22741_0]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [hlam, p22741_0]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [h20413, hlam, p22741_0]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [h20413, h22729, h22732, h22734, hc01, hc12, hlam, hphi, p22741_1]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [h20410, hlam, p22741_1]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [h20412, hlam, p22741_0]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [h16915, h20413, h22729, h22732, h22734, hc01, hc12, hlam, hphi, p22741_1]
          · have p22741_0 := h22741c.1
            have p22741_1 := h22741c.2.1
            have p22741_2 := h22741c.2.2.1
            have p22741_3 := h22741c.2.2.2
            linarith only [hlam, p22741_0]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h23060 | h23060
      · linarith only [h20409, h20413, h23060, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h23062 | h23062
        · linarith only [h20412, h20413, h22735, h22736, h23062, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
        · rcases h0bigk with h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c | h23064c
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [hlam, p23064_0]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [h0, hlam, p23064_1]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [h14396, hlam, p23064_0]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [h16915, hlam, p23064_1]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [h18815, hlam, p23064_1]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            rcases p23064_3 (m.d 0 1) (by simp) with h23070 | h23070
            · linarith only [h0, h23070, hlam]
            · rcases p23064_3 (m.d 0 2) (by simp) with h23072 | h23072
              · rcases p23064_3 (m.d 0 3) (by simp) with h23073 | h23073
                · linarith only [h20408, h23073, hlam]
                · linarith only [h14396, h23073, hlam]
              · linarith only [h0, h23072, hlam]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [hlam, p23064_0]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [h0, h20412, h22735, h22736, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23064_1]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            rcases p23064_3 (m.d 0 1) (by simp) with h23079 | h23079
            · linarith only [h0, h23079, hlam]
            · rcases p23064_3 (m.d 0 2) (by simp) with h23081 | h23081
              · rcases p23064_3 (m.d 0 3) (by simp) with h23082 | h23082
                · linarith only [h20408, h23082, hlam]
                · linarith only [h20411, h23082, hlam]
              · linarith only [h20409, h23081, hlam]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [h0, h20412, h22735, h22736, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23064_1]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            rcases p23064_3 (m.d 0 1) (by simp) with h23087 | h23087
            · linarith only [h14396, h23087, hlam]
            · rcases p23064_3 (m.d 0 2) (by simp) with h23089 | h23089
              · rcases p23064_3 (m.d 0 3) (by simp) with h23090 | h23090
                · rcases p23064_3 (m.d 0 4) (by simp) with h23091 | h23091
                  · linarith only [h20411, h23091, hlam]
                  · linarith only [h16915, h23091, hlam]
                · linarith only [h14396, h23090, hlam]
              · linarith only [h0, h23089, hlam]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [h20408, hlam, p23064_1]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [hlam, p23064_0]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            rcases p23064_3 (m.d 0 1) (by simp) with h23098 | h23098
            · linarith only [h14396, h23098, hlam]
            · rcases p23064_3 (m.d 0 2) (by simp) with h23100 | h23100
              · rcases p23064_3 (m.d 0 3) (by simp) with h23101 | h23101
                · rcases p23064_3 (m.d 0 4) (by simp) with h23102 | h23102
                  · linarith only [h20411, h23102, hlam]
                  · rcases p23064_3 (m.d 0 5) (by simp) with h23104 | h23104
                    · linarith only [h20412, h23104, hlam]
                    · linarith only [h20413, h23104, hlam]
                · linarith only [h20411, h23101, hlam]
              · linarith only [h20409, h23100, hlam]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [h20412, h22735, h22736, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p23064_1]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [h20413, h22734, hc01, hc15, hlam, hphi, p23064_1]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [h20409, hlam, p23064_0]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [h20411, hlam, p23064_0]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [hlam, p23064_0]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [h20413, hlam, p23064_0]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [h20413, h22729, h22732, h22734, hc01, hc12, hlam, hphi, p23064_1]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [h20410, hlam, p23064_1]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [h20412, hlam, p23064_0]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [h16915, h20413, h22729, h22732, h22734, hc01, hc12, hlam, hphi, p23064_1]
          · have p23064_0 := h23064c.1
            have p23064_1 := h23064c.2.1
            have p23064_2 := h23064c.2.2.1
            have p23064_3 := h23064c.2.2.2
            linarith only [hlam, p23064_0]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h23120 | h23120
    · linarith only [h20411, h20413, h22729, h22732, h22734, h22735, h23120, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h23122 | h23122
      · linarith only [h20411, h20413, h22735, h23122, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h23124 | h23124
        · linarith only [h20411, h20413, h23124, hlam]
        · rcases h0bigk with h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c | h23126c
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [hlam, p23126_0]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [h0, hlam, p23126_1]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [h14396, hlam, p23126_0]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [h16915, hlam, p23126_1]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [h18815, hlam, p23126_1]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            rcases p23126_3 (m.d 0 1) (by simp) with h23132 | h23132
            · linarith only [h0, h23132, hlam]
            · rcases p23126_3 (m.d 0 2) (by simp) with h23134 | h23134
              · rcases p23126_3 (m.d 0 3) (by simp) with h23135 | h23135
                · linarith only [h20408, h23135, hlam]
                · linarith only [h14396, h23135, hlam]
              · linarith only [h0, h23134, hlam]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [hlam, p23126_0]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [h0, h20411, h22735, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p23126_1]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            rcases p23126_3 (m.d 0 1) (by simp) with h23141 | h23141
            · linarith only [h0, h23141, hlam]
            · rcases p23126_3 (m.d 0 2) (by simp) with h23143 | h23143
              · rcases p23126_3 (m.d 0 3) (by simp) with h23144 | h23144
                · linarith only [h20408, h23144, hlam]
                · linarith only [h20411, h23144, hlam]
              · linarith only [h20409, h23143, hlam]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            rcases p23126_3 (m.d 0 1) (by simp) with h23148 | h23148
            · linarith only [h0, h23148, hlam]
            · rcases p23126_3 (m.d 0 2) (by simp) with h23150 | h23150
              · rcases p23126_3 (m.d 0 3) (by simp) with h23151 | h23151
                · linarith only [h20408, h23151, hlam]
                · linarith only [h20412, h23151, hlam]
              · linarith only [h20410, h23150, hlam]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            rcases p23126_3 (m.d 0 1) (by simp) with h23155 | h23155
            · linarith only [h14396, h23155, hlam]
            · rcases p23126_3 (m.d 0 2) (by simp) with h23157 | h23157
              · rcases p23126_3 (m.d 0 3) (by simp) with h23158 | h23158
                · rcases p23126_3 (m.d 0 4) (by simp) with h23159 | h23159
                  · linarith only [h20411, h23159, hlam]
                  · linarith only [h16915, h23159, hlam]
                · linarith only [h14396, h23158, hlam]
              · linarith only [h0, h23157, hlam]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [h20408, hlam, p23126_1]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [hlam, p23126_0]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            rcases p23126_3 (m.d 0 1) (by simp) with h23166 | h23166
            · linarith only [h14396, h23166, hlam]
            · rcases p23126_3 (m.d 0 2) (by simp) with h23168 | h23168
              · rcases p23126_3 (m.d 0 3) (by simp) with h23169 | h23169
                · rcases p23126_3 (m.d 0 4) (by simp) with h23170 | h23170
                  · linarith only [h20411, h23170, hlam]
                  · rcases p23126_3 (m.d 0 5) (by simp) with h23172 | h23172
                    · linarith only [h20412, h23172, hlam]
                    · linarith only [h20413, h23172, hlam]
                · linarith only [h20411, h23169, hlam]
              · linarith only [h20409, h23168, hlam]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            rcases p23126_3 (m.d 0 1) (by simp) with h23177 | h23177
            · linarith only [h14396, h23177, hlam]
            · rcases p23126_3 (m.d 0 2) (by simp) with h23179 | h23179
              · rcases p23126_3 (m.d 0 3) (by simp) with h23180 | h23180
                · rcases p23126_3 (m.d 0 4) (by simp) with h23181 | h23181
                  · linarith only [h20411, h23181, hlam]
                  · rcases p23126_3 (m.d 0 5) (by simp) with h23183 | h23183
                    · linarith only [h20412, h23183, hlam]
                    · rcases h2bigk with h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c | h23185c
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [hlam, p23185_0]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [h0, hlam, p23185_1]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [h20408, h20411, h20413, h22735, hlam, p23126_1, p23185_2]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        rcases p23185_3 (m.d 0 2) (by simp) with h23189 | h23189
                        · rcases p23185_3 (m.d 1 2) (by simp) with h23190 | h23190
                          · rcases p23185_3 (m.d 2 3) (by simp) with h23191 | h23191
                            · linarith only [h20408, h23191, hlam]
                            · rcases p23185_3 (m.d 2 4) (by simp) with h23193 | h23193
                              · linarith only [h23193, hlam, p23185_0]
                              · rcases p23185_3 (m.d 2 5) (by simp) with h23195 | h23195
                                · linarith only [h20410, h23195, hlam]
                                · linarith only [h23122, h23195, hlam]
                          · linarith only [h22730, h23190, hlam]
                        · linarith only [h23189, hlam, p23185_0]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        rcases p23185_3 (m.d 0 2) (by simp) with h23200 | h23200
                        · rcases p23185_3 (m.d 1 2) (by simp) with h23201 | h23201
                          · rcases p23185_3 (m.d 2 3) (by simp) with h23202 | h23202
                            · linarith only [h20408, h23202, hlam]
                            · rcases p23185_3 (m.d 2 4) (by simp) with h23204 | h23204
                              · linarith only [h20409, h23204, hlam]
                              · rcases p23185_3 (m.d 2 5) (by simp) with h23206 | h23206
                                · linarith only [h23206, hlam, p23185_0]
                                · rcases h3bigk with h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c | h23208c
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [hlam, p23208_0]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [h14396, hlam, p23208_1]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    rcases p23208_3 (m.d 0 3) (by simp) with h23211 | h23211
                                    · rcases p23208_3 (m.d 1 3) (by simp) with h23212 | h23212
                                      · rcases p23208_3 (m.d 2 3) (by simp) with h23213 | h23213
                                        · linarith only [h20408, h23213, hlam]
                                        · rcases p23208_3 (m.d 3 4) (by simp) with h23215 | h23215
                                          · linarith only [h20411, h23215, hlam]
                                          · linarith only [h22735, h23215, hlam]
                                      · linarith only [h22729, h23212, hlam]
                                    · linarith only [h20408, h23211, hlam]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [h20408, h22735, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p23208_1]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [h20408, h23120, hlam, p23185_2, p23208_1]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [h14396, h22729, hc01, hc12, hlam, hphi, p23208_1]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [hlam, p23208_0]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    rcases p23208_3 (m.d 0 3) (by simp) with h23224 | h23224
                                    · linarith only [h14396, h23224, hlam]
                                    · linarith only [h20408, h23224, hlam]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [h22729, h22735, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p23208_1]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [h22729, h22735, h23124, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p23208_1]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [h20408, hlam, p23208_0]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [h22729, hlam, p23208_0]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [hlam, p23208_0]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [h22735, hlam, p23208_0]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [h23120, hlam, p23208_0]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [h20411, hlam, p23208_0]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [h22732, hlam, p23208_0]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [h20408, h20411, h20413, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p23126_1, p23208_1]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [hlam, p23208_0]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [h23124, hlam, p23208_1]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [h20412, hlam, p23208_0]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [h22733, hlam, p23208_0]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [hc23, hc35, hlam, hphi, p23208_1]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [h0, h20408, h20412, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23126_1, p23208_1]
                                  · have p23208_0 := h23208c.1
                                    have p23208_1 := h23208c.2.1
                                    have p23208_2 := h23208c.2.2.1
                                    have p23208_3 := h23208c.2.2.2
                                    linarith only [hlam, p23208_0]
                          · linarith only [h22731, h23201, hlam]
                        · linarith only [h23200, hlam, p23185_0]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [h20408, h20413, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p23126_1, p23185_1]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [hlam, p23185_0]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [h0, h20408, h20411, h20413, h22735, hlam, p23126_1, p23185_2]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        rcases p23185_3 (m.d 0 2) (by simp) with h23249 | h23249
                        · linarith only [h0, h23249, hlam]
                        · linarith only [h20409, h23249, hlam]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        rcases p23185_3 (m.d 0 2) (by simp) with h23252 | h23252
                        · linarith only [h0, h23252, hlam]
                        · linarith only [h20410, h23252, hlam]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [h20408, hlam, p23185_0]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [h22729, hlam, p23185_0]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [hlam, p23185_0]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [h22735, hlam, p23185_0]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [h23120, hlam, p23185_0]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [h20409, hlam, p23185_0]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [h22730, hlam, p23185_0]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [h0, h20408, h20409, h20413, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p23126_1, p23185_1]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [hlam, p23185_0]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [h23122, hlam, p23185_1]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [h20410, hlam, p23185_0]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [h22731, hlam, p23185_0]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [h0, h20408, h20410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p23126_1, p23185_1]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [h0, h20408, h20412, h23120, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p23126_1, p23185_1]
                      · have p23185_0 := h23185c.1
                        have p23185_1 := h23185c.2.1
                        have p23185_2 := h23185c.2.2.1
                        have p23185_3 := h23185c.2.2.2
                        linarith only [hlam, p23185_0]
                · linarith only [h20412, h23180, hlam]
              · linarith only [h20410, h23179, hlam]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [h20413, h22729, h22732, h22734, hc01, hc12, hlam, hphi, p23126_1]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [h20409, hlam, p23126_0]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [h20411, hlam, p23126_0]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [hlam, p23126_0]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [h20413, hlam, p23126_0]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [h20413, h22729, h22732, h22734, hc01, hc12, hlam, hphi, p23126_1]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [h20410, hlam, p23126_1]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [h20412, hlam, p23126_0]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [h16915, h20413, h22729, h22732, h22734, hc01, hc12, hlam, hphi, p23126_1]
          · have p23126_0 := h23126c.1
            have p23126_1 := h23126c.2.1
            have p23126_2 := h23126c.2.2.1
            have p23126_3 := h23126c.2.2.2
            linarith only [hlam, p23126_0]

end R2N4
