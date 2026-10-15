import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 16662000 in
set_option maxHeartbeats 16662000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s18_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h20408 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h26804 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  rcases m.htr 0 2 5 (by decide) (by decide) with h26805 | h26805
  · rcases m.htr 0 3 4 (by decide) (by decide) with h26806 | h26806
    · rcases m.htr 0 3 5 (by decide) (by decide) with h26807 | h26807
      · rcases m.htr 0 4 5 (by decide) (by decide) with h26808 | h26808
        · rcases m.htr 1 2 3 (by decide) (by decide) with h26809 | h26809
          · rcases m.htr 1 2 4 (by decide) (by decide) with h26810 | h26810
            · rcases m.htr 1 2 5 (by decide) (by decide) with h26811 | h26811
              · rcases m.htr 1 3 4 (by decide) (by decide) with h26812 | h26812
                · rcases m.htr 1 3 5 (by decide) (by decide) with h26813 | h26813
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h26814 | h26814
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h26815 | h26815
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h26816 | h26816
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h26817 | h26817
                          · linarith only [h20408, h26804, h26809, h26817, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h20408, h26804, h26808, h26809, h26817, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h20408, h26805, h26807, h26816, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h20408, h26806, h26815, hlam]
                    · linarith only [h20408, h26804, h26808, h26809, h26814, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h14396, h20408, h26804, h26807, h26808, h26809, h26813, hc01, hc12, hlam, hphi]
                · linarith only [h20408, h26804, h26806, h26809, h26812, hlam]
              · linarith only [h20408, h26805, h26809, h26811, hlam]
            · linarith only [h20408, h26804, h26809, h26810, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h26827 | h26827
            · rcases m.htr 1 2 5 (by decide) (by decide) with h26828 | h26828
              · rcases m.htr 1 3 4 (by decide) (by decide) with h26829 | h26829
                · rcases m.htr 1 3 5 (by decide) (by decide) with h26830 | h26830
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h26831 | h26831
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h26832 | h26832
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h26833 | h26833
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h26834 | h26834
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h26835 | h26835
                            · rcases h0bigk with h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c | h26836c
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [hlam, p26836_0]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [h0, hlam, p26836_1]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [h14396, hlam, p26836_0]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [h16915, hlam, p26836_1]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [h18815, hlam, p26836_1]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [h0, h26809, hc01, hc23, hlam, hphi, ht12, p26836_1]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [hlam, p26836_0]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [h20408, hlam, p26836_0]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [h0, h16915, h26809, hc01, hc23, hlam, hphi, ht12, p26836_1]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [h0, h18815, h26809, hc01, hc23, hlam, hphi, ht12, p26836_1]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                rcases p26836_3 (m.d 0 1) (by simp) with h26847 | h26847
                                · linarith only [h14396, h26847, hlam]
                                · rcases p26836_3 (m.d 0 2) (by simp) with h26849 | h26849
                                  · linarith only [h20408, h26849, hlam]
                                  · linarith only [h0, h26849, hlam]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [h14396, h26804, h26809, h26832, h26835, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p26836_1]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [hlam, p26836_0]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                rcases p26836_3 (m.d 0 1) (by simp) with h26854 | h26854
                                · linarith only [h14396, h26854, hlam]
                                · rcases p26836_3 (m.d 0 2) (by simp) with h26856 | h26856
                                  · linarith only [h20408, h26856, hlam]
                                  · linarith only [h26804, h26856, hlam]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                rcases p26836_3 (m.d 0 1) (by simp) with h26859 | h26859
                                · linarith only [h14396, h26859, hlam]
                                · rcases p26836_3 (m.d 0 2) (by simp) with h26861 | h26861
                                  · linarith only [h20408, h26861, hlam]
                                  · linarith only [h26805, h26861, hlam]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [h0, h26804, h26809, hc01, hc23, hlam, hphi, ht12, p26836_1]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [h26804, hlam, p26836_0]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [h26806, hlam, p26836_0]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [hlam, p26836_0]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [h0, h18815, h26804, h26809, hc01, hc23, hlam, hphi, ht12, p26836_1]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [h0, h26805, h26809, hc01, hc23, hlam, hphi, ht12, p26836_1]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [h26805, hlam, p26836_1]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [h26807, hlam, p26836_0]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [h26808, hlam, p26836_1]
                              · have p26836_0 := h26836c.1
                                have p26836_1 := h26836c.2.1
                                have p26836_2 := h26836c.2.2.1
                                have p26836_3 := h26836c.2.2.2
                                linarith only [hlam, p26836_0]
                            · linarith only [h0, h26804, h26809, h26834, h26835, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h26875 | h26875
                            · linarith only [h26832, h26834, h26875, hlam]
                            · rcases h0bigk with h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c | h26877c
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [hlam, p26877_0]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h0, hlam, p26877_1]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h14396, hlam, p26877_0]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h16915, hlam, p26877_1]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h18815, hlam, p26877_1]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h0, h26809, hc01, hc23, hlam, hphi, ht12, p26877_1]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [hlam, p26877_0]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h20408, hlam, p26877_0]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h0, h16915, h26809, hc01, hc23, hlam, hphi, ht12, p26877_1]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h0, h18815, h26809, hc01, hc23, hlam, hphi, ht12, p26877_1]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                rcases p26877_3 (m.d 0 1) (by simp) with h26888 | h26888
                                · linarith only [h14396, h26888, hlam]
                                · rcases p26877_3 (m.d 0 2) (by simp) with h26890 | h26890
                                  · linarith only [h20408, h26890, hlam]
                                  · linarith only [h0, h26890, hlam]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h14396, h26804, h26808, h26809, h26832, h26834, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p26877_1]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [hlam, p26877_0]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h14396, h26808, h26809, h26832, h26834, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p26877_1]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                rcases p26877_3 (m.d 0 1) (by simp) with h26896 | h26896
                                · linarith only [h14396, h26896, hlam]
                                · rcases p26877_3 (m.d 0 2) (by simp) with h26898 | h26898
                                  · linarith only [h20408, h26898, hlam]
                                  · linarith only [h26805, h26898, hlam]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h0, h26804, h26809, hc01, hc23, hlam, hphi, ht12, p26877_1]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h26804, hlam, p26877_0]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h26806, hlam, p26877_0]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [hlam, p26877_0]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h0, h26804, h26808, h26809, h26832, h26834, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p26877_1]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h0, h26805, h26809, hc01, hc23, hlam, hphi, ht12, p26877_1]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h26805, hlam, p26877_1]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h26807, hlam, p26877_0]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [h26808, hlam, p26877_1]
                              · have p26877_0 := h26877c.1
                                have p26877_1 := h26877c.2.1
                                have p26877_2 := h26877c.2.2.1
                                have p26877_3 := h26877c.2.2.2
                                linarith only [hlam, p26877_0]
                        · linarith only [h0, h26809, h26833, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h26809, h26832, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h16915, h26804, h26808, h26831, hc01, hc12, hlam, hphi]
                  · linarith only [h14396, h26807, h26830, hlam]
                · linarith only [h14396, h26806, h26829, hlam]
              · linarith only [h0, h26805, h26828, hlam]
            · linarith only [h0, h26804, h26827, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h26918 | h26918
          · rcases m.htr 1 2 4 (by decide) (by decide) with h26919 | h26919
            · rcases m.htr 1 2 5 (by decide) (by decide) with h26920 | h26920
              · rcases m.htr 1 3 4 (by decide) (by decide) with h26921 | h26921
                · rcases m.htr 1 3 5 (by decide) (by decide) with h26922 | h26922
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h26923 | h26923
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h26924 | h26924
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h26925 | h26925
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h26926 | h26926
                          · linarith only [h0, h16915, h26804, h26808, h26926, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h26928 | h26928
                            · linarith only [h16915, h20408, h26805, h26808, h26918, h26924, h26926, h26928, hc01, hc12, hlam, hphi]
                            · rcases h0bigk with h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c | h26930c
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [hlam, p26930_0]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h0, hlam, p26930_1]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h14396, hlam, p26930_0]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h16915, hlam, p26930_1]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h18815, hlam, p26930_1]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h20408, h26918, hc01, hc12, hlam, hphi, p26930_1]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [hlam, p26930_0]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h20408, hlam, p26930_0]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h16915, h20408, h26918, hc01, hc12, hlam, hphi, p26930_1]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h20408, h26918, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p26930_1]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h20408, h26918, hc01, hc12, hlam, hphi, p26930_1]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h20408, h26805, h26918, h26926, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p26930_1]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [hlam, p26930_0]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h16915, h20408, h26918, hc01, hc12, hlam, hphi, p26930_1]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h18815, h20408, h26918, hc01, hc12, hlam, hphi, p26930_1]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h26808, h26921, h26923, hc01, hc13, hlam, hphi, p26930_1]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h26804, hlam, p26930_0]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h26806, hlam, p26930_0]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [hlam, p26930_0]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h26808, hlam, p26930_0]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h20408, h26805, h26918, hc01, hc12, hlam, hphi, p26930_1]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h26805, hlam, p26930_1]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h26807, hlam, p26930_0]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [h20408, h26805, h26918, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p26930_1]
                              · have p26930_0 := h26930c.1
                                have p26930_1 := h26930c.2.1
                                have p26930_2 := h26930c.2.2.1
                                have p26930_3 := h26930c.2.2.2
                                linarith only [hlam, p26930_0]
                        · linarith only [h20408, h26807, h26925, hlam]
                      · linarith only [h20408, h26806, h26924, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h26958 | h26958
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h26959 | h26959
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h26960 | h26960
                          · linarith only [h26804, h26808, h26960, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h26962 | h26962
                            · linarith only [h16915, h26923, h26958, h26962, hc01, hc24, hlam, hphi, ht12]
                            · rcases h0bigk with h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c | h26964c
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [hlam, p26964_0]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h0, hlam, p26964_1]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h14396, hlam, p26964_0]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h16915, hlam, p26964_1]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h18815, hlam, p26964_1]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h20408, h26918, hc01, hc12, hlam, hphi, p26964_1]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [hlam, p26964_0]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h20408, hlam, p26964_0]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h16915, h20408, h26918, hc01, hc12, hlam, hphi, p26964_1]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h20408, h26918, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p26964_1]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h20408, h26918, hc01, hc12, hlam, hphi, p26964_1]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h20408, h26805, h26918, h26960, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p26964_1]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [hlam, p26964_0]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h16915, h20408, h26918, hc01, hc12, hlam, hphi, p26964_1]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h18815, h20408, h26918, hc01, hc12, hlam, hphi, p26964_1]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h16915, h26923, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p26964_1]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h26804, hlam, p26964_0]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h26806, hlam, p26964_0]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [hlam, p26964_0]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h26808, hlam, p26964_0]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h20408, h26805, h26918, hc01, hc12, hlam, hphi, p26964_1]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h26805, hlam, p26964_1]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h26807, hlam, p26964_0]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [h20408, h26805, h26918, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p26964_1]
                              · have p26964_0 := h26964c.1
                                have p26964_1 := h26964c.2.1
                                have p26964_2 := h26964c.2.2.1
                                have p26964_3 := h26964c.2.2.2
                                linarith only [hlam, p26964_0]
                        · linarith only [h20408, h26807, h26959, hlam]
                      · linarith only [h20408, h26806, h26958, hlam]
                  · linarith only [h14396, h20408, h26805, h26807, h26922, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h20408, h26804, h26806, h26918, h26921, hlam]
              · linarith only [h20408, h26918, h26920, hc02, hc25, hlam, hphi]
            · linarith only [h20408, h26804, h26918, h26919, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h26996 | h26996
            · rcases m.htr 1 2 5 (by decide) (by decide) with h26997 | h26997
              · rcases m.htr 1 3 4 (by decide) (by decide) with h26998 | h26998
                · rcases m.htr 1 3 5 (by decide) (by decide) with h26999 | h26999
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h27000 | h27000
                    · linarith only [h16915, h26808, h26918, h26996, h27000, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h27002 | h27002
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h27003 | h27003
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h27004 | h27004
                          · linarith only [h0, h26804, h26918, h27000, h27004, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h27006 | h27006
                            · linarith only [h16915, h27000, h27006, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h0bigk with h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c | h27008c
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [hlam, p27008_0]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [h0, hlam, p27008_1]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [h14396, hlam, p27008_0]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [h16915, hlam, p27008_1]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [h18815, hlam, p27008_1]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [h0, h26918, hc01, hc23, hlam, hphi, ht12, p27008_1]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [hlam, p27008_0]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [h20408, hlam, p27008_0]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [h0, h16915, h26918, hc01, hc23, hlam, hphi, ht12, p27008_1]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [h0, h18815, h26918, hc01, hc23, hlam, hphi, ht12, p27008_1]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                rcases p27008_3 (m.d 0 1) (by simp) with h27019 | h27019
                                · linarith only [h14396, h27019, hlam]
                                · rcases p27008_3 (m.d 0 2) (by simp) with h27021 | h27021
                                  · linarith only [h20408, h27021, hlam]
                                  · linarith only [h0, h27021, hlam]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                rcases p27008_3 (m.d 0 1) (by simp) with h27024 | h27024
                                · linarith only [h14396, h27024, hlam]
                                · rcases p27008_3 (m.d 0 2) (by simp) with h27026 | h27026
                                  · linarith only [h20408, h27026, hlam]
                                  · rcases p27008_3 (m.d 0 3) (by simp) with h27028 | h27028
                                    · rcases p27008_3 (m.d 0 4) (by simp) with h27029 | h27029
                                      · linarith only [h26806, h27029, hlam]
                                      · rcases p27008_3 (m.d 0 5) (by simp) with h27031 | h27031
                                        · linarith only [h26807, h27031, hlam]
                                        · rcases h2bigk with h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c | h27033c
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [hlam, p27033_0]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [h0, hlam, p27033_1]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [h20408, hlam, p27033_0]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [h14396, h26918, h27002, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p27008_1, p27033_1]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [h14396, h26918, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p27008_1, p27033_1]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [h26918, hc02, hc23, hlam, hphi, p27033_1]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [hlam, p27033_0]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [h26918, hlam, p27033_0]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            rcases p27033_3 (m.d 0 2) (by simp) with h27042 | h27042
                                            · linarith only [h0, h27042, hlam]
                                            · linarith only [h26804, h27042, hlam]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            rcases p27033_3 (m.d 0 2) (by simp) with h27045 | h27045
                                            · linarith only [h0, h27045, hlam]
                                            · linarith only [h26805, h27045, hlam]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            rcases p27033_3 (m.d 0 2) (by simp) with h27048 | h27048
                                            · linarith only [h27048, hlam, p27033_0]
                                            · rcases p27033_3 (m.d 1 2) (by simp) with h27050 | h27050
                                              · linarith only [h26918, h27050, hlam]
                                              · linarith only [h0, h27050, hlam]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p27033_1]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [hlam, p27033_0]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [h14396, h26805, h26918, h27004, hlam, p27008_1, p27033_2]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [h14396, h26805, h26918, hlam, p27008_1, p27033_2]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [h26804, hlam, p27033_0]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [h26996, hlam, p27033_0]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [h27002, hlam, p27033_1]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [hlam, p27033_0]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [h27004, hlam, p27033_1]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [h26805, hlam, p27033_0]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [h26997, hlam, p27033_0]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [h27003, hlam, p27033_1]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [h14396, h26805, h26918, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p27008_1, p27033_1]
                                          · have p27033_0 := h27033c.1
                                            have p27033_1 := h27033c.2.1
                                            have p27033_2 := h27033c.2.2.1
                                            have p27033_3 := h27033c.2.2.2
                                            linarith only [hlam, p27033_0]
                                    · linarith only [h20408, h27028, hlam]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [hlam, p27008_0]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                rcases p27008_3 (m.d 0 1) (by simp) with h27069 | h27069
                                · linarith only [h14396, h27069, hlam]
                                · rcases p27008_3 (m.d 0 2) (by simp) with h27071 | h27071
                                  · linarith only [h20408, h27071, hlam]
                                  · linarith only [h26804, h27071, hlam]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                rcases p27008_3 (m.d 0 1) (by simp) with h27074 | h27074
                                · linarith only [h14396, h27074, hlam]
                                · rcases p27008_3 (m.d 0 2) (by simp) with h27076 | h27076
                                  · linarith only [h20408, h27076, hlam]
                                  · linarith only [h26805, h27076, hlam]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [h16915, h27000, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p27008_1]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [h26804, hlam, p27008_0]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [h26806, hlam, p27008_0]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [hlam, p27008_0]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [h26808, hlam, p27008_0]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [h20408, h26805, hc01, hc23, hlam, hphi, ht12, p27008_1]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [h26805, hlam, p27008_1]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [h26807, hlam, p27008_0]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [h16915, h20408, h26805, hc01, hc23, hlam, hphi, ht12, p27008_1]
                              · have p27008_0 := h27008c.1
                                have p27008_1 := h27008c.2.1
                                have p27008_2 := h27008c.2.2.1
                                have p27008_3 := h27008c.2.2.2
                                linarith only [hlam, p27008_0]
                        · linarith only [h0, h26918, h27003, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h16915, h26918, h26997, h27000, h27002, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h14396, h18815, h26807, h26918, h26997, h26999, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h14396, h20408, h26804, h26806, h26998, hlam]
              · linarith only [h0, h14396, h20408, h26805, h26997, hc01, hc13, hlam, hphi]
            · linarith only [h0, h26804, h26996, hlam]
      · linarith only [h20408, h26805, h26807, hlam]
    · linarith only [h20408, h26804, h26806, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h27097 | h27097
    · rcases m.htr 0 3 5 (by decide) (by decide) with h27098 | h27098
      · rcases m.htr 0 4 5 (by decide) (by decide) with h27099 | h27099
        · linarith only [h26804, h26805, h27099, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h27101 | h27101
          · rcases m.htr 1 2 4 (by decide) (by decide) with h27102 | h27102
            · rcases m.htr 1 2 5 (by decide) (by decide) with h27103 | h27103
              · rcases m.htr 1 3 4 (by decide) (by decide) with h27104 | h27104
                · rcases m.htr 1 3 5 (by decide) (by decide) with h27105 | h27105
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h27106 | h27106
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h27107 | h27107
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h27108 | h27108
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h27109 | h27109
                          · linarith only [h26804, h26805, h27099, h27101, h27108, h27109, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h27111 | h27111
                            · linarith only [h26804, h26805, h27107, h27109, h27111, hlam]
                            · rcases h0bigk with h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c | h27113c
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [hlam, p27113_0]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h0, hlam, p27113_1]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h14396, hlam, p27113_0]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h16915, hlam, p27113_1]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h18815, hlam, p27113_1]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h26805, h27101, h27104, h27106, h27109, hc01, hc12, hlam, hphi, p27113_1]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [hlam, p27113_0]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h20408, hlam, p27113_0]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h16915, h26805, h27101, h27104, h27106, h27109, hc01, hc12, hlam, hphi, p27113_1]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h26805, hlam, p27113_0]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h20408, h27101, hc01, hc12, hlam, hphi, p27113_1]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h20408, h26804, h27101, h27107, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p27113_1]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [hlam, p27113_0]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h16915, h20408, h27101, hc01, hc12, hlam, hphi, p27113_1]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h18815, h20408, h27101, hc01, hc12, hlam, hphi, p27113_1]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h20408, h26804, h27101, hc01, hc12, hlam, hphi, p27113_1]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h26804, hlam, p27113_0]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h27097, hlam, p27113_0]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [hlam, p27113_0]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h27099, hlam, p27113_0]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h26805, h27101, h27104, h27106, h27109, hc01, hc12, hlam, hphi, p27113_1]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h0, h26805, h27101, h27104, h27106, h27109, hc01, hc12, hlam, hphi, p27113_1]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h27098, hlam, p27113_0]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [h16915, h26805, h27101, h27104, h27106, h27109, hc01, hc12, hlam, hphi, p27113_1]
                              · have p27113_0 := h27113c.1
                                have p27113_1 := h27113c.2.1
                                have p27113_2 := h27113c.2.2.1
                                have p27113_3 := h27113c.2.2.2
                                linarith only [hlam, p27113_0]
                        · linarith only [h20408, h27098, h27108, hlam]
                      · linarith only [h20408, h27097, h27107, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h27141 | h27141
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h27142 | h27142
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h27143 | h27143
                          · linarith only [h16915, h26804, h27106, h27143, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h27145 | h27145
                            · linarith only [h26804, h26805, h27101, h27106, h27141, h27142, h27145, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases h0bigk with h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c | h27147c
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [hlam, p27147_0]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h0, hlam, p27147_1]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h14396, hlam, p27147_0]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h16915, hlam, p27147_1]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h18815, hlam, p27147_1]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h26805, h27101, h27142, hc01, hc12, hlam, hphi, p27147_1]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [hlam, p27147_0]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h20408, hlam, p27147_0]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h26805, h27101, h27142, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p27147_1]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h26805, hlam, p27147_0]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h20408, h27101, hc01, hc12, hlam, hphi, p27147_1]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h20408, h26804, h27101, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p27147_1]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [hlam, p27147_0]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h16915, h20408, h27101, hc01, hc12, hlam, hphi, p27147_1]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h18815, h20408, h27101, hc01, hc12, hlam, hphi, p27147_1]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h20408, h26804, h27101, hc01, hc12, hlam, hphi, p27147_1]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h26804, hlam, p27147_0]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h27097, hlam, p27147_0]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [hlam, p27147_0]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h27099, hlam, p27147_0]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h26805, h27101, h27142, hc01, hc12, hlam, hphi, p27147_1]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h0, h26805, h27101, h27142, hc01, hc12, hlam, hphi, p27147_1]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h27098, hlam, p27147_0]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [h16915, h26805, h27101, h27142, hc01, hc12, hlam, hphi, p27147_1]
                              · have p27147_0 := h27147c.1
                                have p27147_1 := h27147c.2.1
                                have p27147_2 := h27147c.2.2.1
                                have p27147_3 := h27147c.2.2.2
                                linarith only [hlam, p27147_0]
                        · linarith only [h20408, h27098, h27142, hlam]
                      · linarith only [h20408, h27097, h27141, hlam]
                  · linarith only [h14396, h27098, h27105, hlam]
                · linarith only [h14396, h20408, h26804, h27097, h27098, h27101, h27104, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h20408, h26804, h27101, h27103, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h20408, h26804, h27101, h27102, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h27179 | h27179
            · rcases m.htr 1 2 5 (by decide) (by decide) with h27180 | h27180
              · linarith only [h26804, h26805, h27101, h27180, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h27182 | h27182
                · rcases m.htr 1 3 5 (by decide) (by decide) with h27183 | h27183
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h27184 | h27184
                    · linarith only [h16915, h27099, h27101, h27179, h27184, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h27186 | h27186
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h27187 | h27187
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h27188 | h27188
                          · linarith only [h0, h26804, h27180, h27184, h27187, h27188, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h27190 | h27190
                            · linarith only [h0, h27180, h27188, h27190, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h0bigk with h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c | h27192c
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [hlam, p27192_0]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [h0, hlam, p27192_1]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [h14396, hlam, p27192_0]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [h16915, hlam, p27192_1]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [h18815, hlam, p27192_1]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [h0, h27180, h27187, hc01, hc23, hlam, hphi, ht12, p27192_1]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [hlam, p27192_0]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [h20408, hlam, p27192_0]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [h0, h16915, h27180, h27188, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p27192_1]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [h26805, hlam, p27192_0]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                rcases p27192_3 (m.d 0 1) (by simp) with h27203 | h27203
                                · linarith only [h14396, h27203, hlam]
                                · rcases p27192_3 (m.d 0 2) (by simp) with h27205 | h27205
                                  · linarith only [h20408, h27205, hlam]
                                  · linarith only [h0, h27205, hlam]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                rcases p27192_3 (m.d 0 1) (by simp) with h27208 | h27208
                                · linarith only [h14396, h27208, hlam]
                                · rcases p27192_3 (m.d 0 2) (by simp) with h27210 | h27210
                                  · linarith only [h20408, h27210, hlam]
                                  · rcases p27192_3 (m.d 0 3) (by simp) with h27212 | h27212
                                    · rcases p27192_3 (m.d 0 4) (by simp) with h27213 | h27213
                                      · linarith only [h27097, h27213, hlam]
                                      · rcases p27192_3 (m.d 0 5) (by simp) with h27215 | h27215
                                        · linarith only [h27098, h27215, hlam]
                                        · linarith only [h26805, h27215, hlam]
                                    · linarith only [h20408, h27212, hlam]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [hlam, p27192_0]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                rcases p27192_3 (m.d 0 1) (by simp) with h27220 | h27220
                                · linarith only [h14396, h27220, hlam]
                                · rcases p27192_3 (m.d 0 2) (by simp) with h27222 | h27222
                                  · linarith only [h20408, h27222, hlam]
                                  · linarith only [h26804, h27222, hlam]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                rcases p27192_3 (m.d 0 1) (by simp) with h27225 | h27225
                                · linarith only [h14396, h27225, hlam]
                                · rcases p27192_3 (m.d 0 2) (by simp) with h27227 | h27227
                                  · linarith only [h20408, h27227, hlam]
                                  · rcases p27192_3 (m.d 0 3) (by simp) with h27229 | h27229
                                    · rcases p27192_3 (m.d 0 4) (by simp) with h27230 | h27230
                                      · linarith only [h27097, h27230, hlam]
                                      · rcases p27192_3 (m.d 0 5) (by simp) with h27232 | h27232
                                        · linarith only [h27098, h27232, hlam]
                                        · rcases h2bigk with h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c | h27234c
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [hlam, p27234_0]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h0, hlam, p27234_1]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h20408, hlam, p27234_0]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h14396, h26805, h27101, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p27192_1, p27234_1]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h26805, hlam, p27234_0]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h27180, hc02, hc25, hlam, hphi, p27234_1]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [hlam, p27234_0]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h27101, hlam, p27234_0]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h27180, h27186, h27188, hc34, hc45, hlam, hphi, p27234_1]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h27180, hlam, p27234_0]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            rcases p27234_3 (m.d 0 2) (by simp) with h27245 | h27245
                                            · linarith only [h27245, hlam, p27234_0]
                                            · rcases p27234_3 (m.d 1 2) (by simp) with h27247 | h27247
                                              · linarith only [h27101, h27247, hlam]
                                              · linarith only [h0, h27247, hlam]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p27234_1]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [hlam, p27234_0]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h14396, h26804, h26805, h27101, hlam, p27192_1, p27234_2]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h26805, hc02, hc23, hlam, hphi, p27234_1]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h26804, hlam, p27234_0]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h27179, hlam, p27234_0]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h27186, hlam, p27234_1]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [hlam, p27234_0]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h27188, hlam, p27234_1]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h26804, h27186, h27188, hc34, hc45, hlam, hphi, p27234_1]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h16915, h27179, hc01, hc25, hlam, hphi, ht12, p27234_1]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [h27187, hlam, p27234_1]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            rcases p27234_3 (m.d 0 2) (by simp) with h27262 | h27262
                                            · linarith only [h26805, h27262, hlam]
                                            · linarith only [h26804, h27262, hlam]
                                          · have p27234_0 := h27234c.1
                                            have p27234_1 := h27234c.2.1
                                            have p27234_2 := h27234c.2.2.1
                                            have p27234_3 := h27234c.2.2.2
                                            linarith only [hlam, p27234_0]
                                    · linarith only [h27098, h27229, hlam]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [h20408, h26804, hc01, hc23, hlam, hphi, ht12, p27192_1]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [h26804, hlam, p27192_0]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [h27097, hlam, p27192_0]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [hlam, p27192_0]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [h27099, hlam, p27192_0]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                rcases p27192_3 (m.d 0 1) (by simp) with h27272 | h27272
                                · linarith only [h18815, h27272, hlam]
                                · rcases p27192_3 (m.d 0 2) (by simp) with h27274 | h27274
                                  · linarith only [h26805, h27274, hlam]
                                  · linarith only [h0, h27274, hlam]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [h18815, h26804, h27180, h27186, h27188, hc34, hc45, hlam, hphi, p27192_1]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [h27098, hlam, p27192_0]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                rcases p27192_3 (m.d 0 1) (by simp) with h27279 | h27279
                                · linarith only [h18815, h27279, hlam]
                                · rcases p27192_3 (m.d 0 2) (by simp) with h27281 | h27281
                                  · linarith only [h26805, h27281, hlam]
                                  · linarith only [h26804, h27281, hlam]
                              · have p27192_0 := h27192c.1
                                have p27192_1 := h27192c.2.1
                                have p27192_2 := h27192c.2.2.1
                                have p27192_3 := h27192c.2.2.2
                                linarith only [hlam, p27192_0]
                        · linarith only [h14396, h27098, h27101, h27187, hlam]
                      · linarith only [h14396, h27097, h27101, h27186, hlam]
                  · linarith only [h14396, h27098, h27183, hlam]
                · linarith only [h14396, h27097, h27182, hlam]
            · linarith only [h0, h26804, h27179, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h27290 | h27290
        · linarith only [h20408, h26804, h27098, h27290, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h27292 | h27292
          · rcases m.htr 1 2 4 (by decide) (by decide) with h27293 | h27293
            · rcases m.htr 1 2 5 (by decide) (by decide) with h27294 | h27294
              · rcases m.htr 1 3 4 (by decide) (by decide) with h27295 | h27295
                · rcases m.htr 1 3 5 (by decide) (by decide) with h27296 | h27296
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h27297 | h27297
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h27298 | h27298
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h27299 | h27299
                        · linarith only [h20408, h26804, h27098, h27292, h27299, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h20408, h26804, h27296, h27298, h27299, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h20408, h27097, h27298, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h27303 | h27303
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h27304 | h27304
                        · linarith only [h14396, h27098, h27292, h27304, hc01, hc12, hlam, hphi]
                        · linarith only [h20408, h26804, h27292, h27296, h27303, h27304, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h20408, h27097, h27303, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h27308 | h27308
                    · linarith only [h16915, h27290, h27295, h27296, h27308, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h27310 | h27310
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h27311 | h27311
                        · linarith only [h27292, h27296, h27311, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h27313 | h27313
                          · linarith only [h0, h18815, h26804, h27308, h27313, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h27315 | h27315
                            · linarith only [h16915, h20408, h26804, h27292, h27296, h27308, h27310, h27315, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h20408, h26804, h27292, h27296, h27310, h27315, hc34, hc45, hlam, hphi]
                      · linarith only [h20408, h26804, h27097, h27310, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h20408, h26804, h27097, h27292, h27295, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h20408, h27292, h27294, hc02, hc25, hlam, hphi]
            · linarith only [h20408, h26804, h27292, h27293, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h27322 | h27322
            · rcases m.htr 1 2 5 (by decide) (by decide) with h27323 | h27323
              · linarith only [h26804, h26805, h27292, h27323, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h27325 | h27325
                · rcases m.htr 1 3 5 (by decide) (by decide) with h27326 | h27326
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h27327 | h27327
                    · linarith only [h16915, h27290, h27322, h27323, h27327, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h27329 | h27329
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h27330 | h27330
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h27331 | h27331
                          · linarith only [h0, h26804, h27323, h27327, h27330, h27331, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h27333 | h27333
                            · linarith only [h20408, h26804, h27098, h27292, h27323, h27326, h27329, h27331, h27333, hc12, hc23, hlam, hphi]
                            · rcases h0bigk with h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c | h27335c
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [hlam, p27335_0]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h0, hlam, p27335_1]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h14396, hlam, p27335_0]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h16915, hlam, p27335_1]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h18815, hlam, p27335_1]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h20408, h27098, h27292, h27326, hc01, hc23, hlam, hphi, ht12, p27335_1]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [hlam, p27335_0]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h20408, hlam, p27335_0]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h16915, h20408, h27098, h27292, h27326, hc01, hc23, hlam, hphi, ht12, p27335_1]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h26805, hlam, p27335_0]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h27098, h27292, h27326, hc01, hc23, hlam, hphi, ht12, p27335_1]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h26804, h27098, h27292, h27326, h27329, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p27335_1]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [hlam, p27335_0]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h16915, h27098, h27292, h27326, hc01, hc23, hlam, hphi, ht12, p27335_1]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h27098, hlam, p27335_1]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h16915, h27322, h27323, hc01, hc25, hlam, hphi, ht12, p27335_1]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h26804, hlam, p27335_0]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h27097, hlam, p27335_0]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [hlam, p27335_0]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h27290, hlam, p27335_0]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h27098, h27292, h27326, hc01, hc23, hlam, hphi, ht12, p27335_1]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h26804, h27098, h27292, h27326, h27329, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p27335_1]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h14396, h27098, h27292, h27326, hc01, hc23, hlam, hphi, ht12, p27335_1]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [h16915, h27098, h27292, h27326, hc01, hc23, hlam, hphi, ht12, p27335_1]
                              · have p27335_0 := h27335c.1
                                have p27335_1 := h27335c.2.1
                                have p27335_2 := h27335c.2.2.1
                                have p27335_3 := h27335c.2.2.2
                                linarith only [hlam, p27335_0]
                        · linarith only [h27292, h27326, h27330, hlam]
                      · linarith only [h14396, h27097, h27292, h27329, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h27363 | h27363
                    · linarith only [h16915, h27290, h27292, h27322, h27326, h27363, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h27365 | h27365
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h27366 | h27366
                        · linarith only [h0, h27292, h27326, h27366, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h16915, h27292, h27322, h27366, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h16915, h27292, h27322, h27365, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h14396, h20408, h26804, h27097, h27325, hlam]
            · linarith only [h0, h14396, h20408, h26804, h27322, hc01, hc13, hlam, hphi]
    · linarith only [h20408, h26804, h27097, hlam]

end R2N4
