import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12204000 in
set_option maxHeartbeats 12204000 in
theorem r1l7_11_23_L_I_H_I_s12_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h12794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h12795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0 := hg0
  have h11385 := hg11385
  rcases m.htr 0 2 3 (by decide) (by decide) with h12796 | h12796
  · rcases m.htr 0 2 4 (by decide) (by decide) with h12797 | h12797
    · rcases m.htr 0 3 4 (by decide) (by decide) with h12798 | h12798
      · rcases m.htr 0 3 5 (by decide) (by decide) with h12799 | h12799
        · rcases m.htr 0 4 5 (by decide) (by decide) with h12800 | h12800
          · rcases m.htr 1 2 3 (by decide) (by decide) with h12801 | h12801
            · rcases m.htr 1 2 4 (by decide) (by decide) with h12802 | h12802
              · rcases m.htr 1 2 5 (by decide) (by decide) with h12803 | h12803
                · rcases m.htr 1 3 4 (by decide) (by decide) with h12804 | h12804
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h12805 | h12805
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h12806 | h12806
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h12807 | h12807
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12808 | h12808
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h12809 | h12809
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h12810 | h12810
                              · rcases h1bigk with h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c | h12811c
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [hlam, p12811_0]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [h0, hlam, p12811_0]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [h11385, hlam, p12811_0]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [h11385, h12802, h12807, h12810, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p12811_1]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  rcases p12811_3 (m.d 0 1) (by simp) with h12816 | h12816
                                  · rcases p12811_3 (m.d 1 2) (by simp) with h12817 | h12817
                                    · rcases p12811_3 (m.d 1 3) (by simp) with h12818 | h12818
                                      · rcases p12811_3 (m.d 1 4) (by simp) with h12819 | h12819
                                        · linarith only [h12794, h12819, hlam]
                                        · linarith only [h12806, h12819, hlam]
                                      · linarith only [h12805, h12818, hlam]
                                    · linarith only [h12803, h12817, hlam]
                                  · linarith only [h12816, hlam, p12811_0]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [h12794, h12802, h12807, h12810, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12811_1]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [hlam, p12811_0]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [h11385, hc01, hc12, hlam, hphi, p12811_1]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  rcases p12811_3 (m.d 0 1) (by simp) with h12828 | h12828
                                  · linarith only [h0, h12828, hlam]
                                  · linarith only [h12794, h12828, hlam]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  rcases p12811_3 (m.d 0 1) (by simp) with h12831 | h12831
                                  · linarith only [h0, h12831, hlam]
                                  · linarith only [h12795, h12831, hlam]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [h12794, h12801, h12802, h12807, h12810, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12811_1]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [h12801, hlam, p12811_1]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [hlam, p12811_0]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  rcases p12811_3 (m.d 0 1) (by simp) with h12837 | h12837
                                  · linarith only [h11385, h12837, hlam]
                                  · linarith only [h12794, h12837, hlam]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  rcases p12811_3 (m.d 0 1) (by simp) with h12840 | h12840
                                  · linarith only [h11385, h12840, hlam]
                                  · linarith only [h12795, h12840, hlam]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [h12794, hlam, p12811_0]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [h12802, hlam, p12811_1]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [h12804, hlam, p12811_0]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [hlam, p12811_0]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [h0, h12794, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p12811_1]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [h12795, hlam, p12811_0]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [h12803, hlam, p12811_1]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [h12805, hlam, p12811_0]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [h12806, hlam, p12811_0]
                                · have p12811_0 := h12811c.1
                                  have p12811_1 := h12811c.2.1
                                  have p12811_2 := h12811c.2.2.1
                                  have p12811_3 := h12811c.2.2.2
                                  linarith only [hlam, p12811_0]
                              · linarith only [h11385, h12794, h12801, h12802, h12809, h12810, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h11385, h12794, h12801, h12806, h12809, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h11385, h12794, h12801, h12805, h12806, h12807, h12808, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12856 | h12856
                          · linarith only [h11385, h12794, h12801, h12804, h12807, h12856, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h12858 | h12858
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h12859 | h12859
                              · rcases h1bigk with h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c | h12860c
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [hlam, p12860_0]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [h0, hlam, p12860_0]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [h11385, hlam, p12860_0]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [h11385, h12801, h12805, h12806, h12856, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12860_1]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [h11385, h12801, h12805, h12856, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12860_1]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [h12794, h12805, h12806, h12856, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12860_1]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [hlam, p12860_0]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [h11385, hc01, hc12, hlam, hphi, p12860_1]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  rcases p12860_3 (m.d 0 1) (by simp) with h12869 | h12869
                                  · linarith only [h0, h12869, hlam]
                                  · linarith only [h12794, h12869, hlam]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  rcases p12860_3 (m.d 0 1) (by simp) with h12872 | h12872
                                  · linarith only [h0, h12872, hlam]
                                  · linarith only [h12795, h12872, hlam]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [h12794, h12805, h12806, h12856, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12860_1]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [h12801, hlam, p12860_1]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [hlam, p12860_0]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  rcases p12860_3 (m.d 0 1) (by simp) with h12878 | h12878
                                  · linarith only [h11385, h12878, hlam]
                                  · linarith only [h12794, h12878, hlam]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  rcases p12860_3 (m.d 0 1) (by simp) with h12881 | h12881
                                  · linarith only [h11385, h12881, hlam]
                                  · linarith only [h12795, h12881, hlam]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [h12794, hlam, p12860_0]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [h12802, hlam, p12860_1]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [h12804, hlam, p12860_0]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [hlam, p12860_0]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [h12794, h12805, h12856, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12860_1]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [h12795, hlam, p12860_0]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [h12803, hlam, p12860_1]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [h12805, hlam, p12860_0]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [h12806, hlam, p12860_0]
                                · have p12860_0 := h12860c.1
                                  have p12860_1 := h12860c.2.1
                                  have p12860_2 := h12860c.2.2.1
                                  have p12860_3 := h12860c.2.2.2
                                  linarith only [hlam, p12860_0]
                              · linarith only [h11385, h12794, h12801, h12802, h12858, h12859, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h11385, h12794, h12801, h12806, h12858, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h12896 | h12896
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12897 | h12897
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h12898 | h12898
                            · linarith only [h12802, h12806, h12898, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h12900 | h12900
                              · linarith only [h12802, h12806, h12896, h12900, hlam]
                              · rcases h1bigk with h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c | h12902c
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [hlam, p12902_0]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [h0, hlam, p12902_0]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [h11385, hlam, p12902_0]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  rcases p12902_3 (m.d 0 1) (by simp) with h12906 | h12906
                                  · rcases p12902_3 (m.d 1 2) (by simp) with h12907 | h12907
                                    · rcases p12902_3 (m.d 1 3) (by simp) with h12908 | h12908
                                      · rcases p12902_3 (m.d 1 4) (by simp) with h12909 | h12909
                                        · linarith only [h12909, hlam, p12902_0]
                                        · rcases p12902_3 (m.d 1 5) (by simp) with h12911 | h12911
                                          · linarith only [h12795, h12911, hlam]
                                          · linarith only [h12806, h12911, hlam]
                                      · linarith only [h12804, h12908, hlam]
                                    · linarith only [h12802, h12907, hlam]
                                  · linarith only [h12906, hlam, p12902_0]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  rcases p12902_3 (m.d 0 1) (by simp) with h12917 | h12917
                                  · rcases p12902_3 (m.d 1 2) (by simp) with h12918 | h12918
                                    · rcases p12902_3 (m.d 1 3) (by simp) with h12919 | h12919
                                      · rcases p12902_3 (m.d 1 4) (by simp) with h12920 | h12920
                                        · linarith only [h12794, h12920, hlam]
                                        · rcases p12902_3 (m.d 1 5) (by simp) with h12922 | h12922
                                          · linarith only [h12922, hlam, p12902_0]
                                          · rcases h3bigk with h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c | h12924c
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [hlam, p12924_0]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [h11385, hlam, p12924_1]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [h0, h12796, h12897, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p12924_1]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              rcases p12924_3 (m.d 0 3) (by simp) with h12928 | h12928
                                              · rcases p12924_3 (m.d 1 3) (by simp) with h12929 | h12929
                                                · rcases p12924_3 (m.d 2 3) (by simp) with h12930 | h12930
                                                  · linarith only [h12796, h12930, hlam]
                                                  · linarith only [h12896, h12930, hlam]
                                                · linarith only [h12804, h12929, hlam]
                                              · linarith only [h12928, hlam, p12924_0]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              rcases p12924_3 (m.d 0 3) (by simp) with h12935 | h12935
                                              · rcases p12924_3 (m.d 1 3) (by simp) with h12936 | h12936
                                                · rcases p12924_3 (m.d 2 3) (by simp) with h12937 | h12937
                                                  · linarith only [h12796, h12937, hlam]
                                                  · linarith only [h12897, h12937, hlam]
                                                · linarith only [h12805, h12936, hlam]
                                              · linarith only [h12935, hlam, p12924_0]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [h11385, h12801, hc01, hc12, hlam, hphi, p12924_1]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [hlam, p12924_0]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [h12801, h12897, h12900, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12924_1]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              rcases p12924_3 (m.d 0 3) (by simp) with h12945 | h12945
                                              · linarith only [h11385, h12945, hlam]
                                              · linarith only [h12798, h12945, hlam]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              rcases p12924_3 (m.d 0 3) (by simp) with h12948 | h12948
                                              · linarith only [h11385, h12948, hlam]
                                              · linarith only [h12799, h12948, hlam]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [h12796, hlam, p12924_0]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [h12801, hlam, p12924_0]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [hlam, p12924_0]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [h0, h12796, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12924_1]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [h0, h12796, h12900, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12924_1]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [h12798, hlam, p12924_0]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [h12804, hlam, p12924_0]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [h12896, hlam, p12924_0]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [hlam, p12924_0]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [h12900, hlam, p12924_1]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [h12799, hlam, p12924_0]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [h12805, hlam, p12924_0]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [h12897, hlam, p12924_0]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [h11385, h12799, h12801, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12924_1]
                                            · have p12924_0 := h12924c.1
                                              have p12924_1 := h12924c.2.1
                                              have p12924_2 := h12924c.2.2.1
                                              have p12924_3 := h12924c.2.2.2
                                              linarith only [hlam, p12924_0]
                                      · linarith only [h12805, h12919, hlam]
                                    · linarith only [h12803, h12918, hlam]
                                  · linarith only [h12917, hlam, p12902_0]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [h12794, h12800, h12802, h12806, h12896, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12902_1]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [hlam, p12902_0]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [h11385, h12794, h12800, h12802, h12806, h12896, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12902_1]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [h0, h12794, h12800, h12806, hlam, p12902_2]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  rcases p12902_3 (m.d 0 1) (by simp) with h12973 | h12973
                                  · linarith only [h0, h12973, hlam]
                                  · linarith only [h12795, h12973, hlam]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [h12794, h12800, h12801, h12802, h12806, h12896, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12902_1]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [h12801, hlam, p12902_1]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [hlam, p12902_0]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [h11385, h12794, h12800, h12806, hlam, p12902_2]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  rcases p12902_3 (m.d 0 1) (by simp) with h12980 | h12980
                                  · linarith only [h11385, h12980, hlam]
                                  · linarith only [h12795, h12980, hlam]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [h12794, hlam, p12902_0]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [h12802, hlam, p12902_1]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [h12804, hlam, p12902_0]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [hlam, p12902_0]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [h12806, hlam, p12902_1]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [h12795, hlam, p12902_0]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [h12803, hlam, p12902_1]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [h12805, hlam, p12902_0]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [h11385, h12795, h12802, h12896, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12902_1]
                                · have p12902_0 := h12902c.1
                                  have p12902_1 := h12902c.2.1
                                  have p12902_2 := h12902c.2.2.1
                                  have p12902_3 := h12902c.2.2.2
                                  linarith only [hlam, p12902_0]
                          · linarith only [h11385, h12794, h12800, h12801, h12805, h12806, h12896, h12897, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h11385, h12794, h12800, h12801, h12804, h12806, h12896, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h11385, h12794, h12796, h12799, h12802, h12805, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h11385, h12798, h12804, hlam]
                · linarith only [h0, h12795, h12803, hlam]
              · linarith only [h0, h12797, h12802, hlam]
            · linarith only [h0, h12796, h12801, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13000 | h13000
            · rcases m.htr 1 2 4 (by decide) (by decide) with h13001 | h13001
              · rcases m.htr 1 2 5 (by decide) (by decide) with h13002 | h13002
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13003 | h13003
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h13004 | h13004
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13005 | h13005
                      · linarith only [h0, h12794, h12800, h13005, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h13007 | h13007
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13008 | h13008
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13009 | h13009
                            · linarith only [h12794, h12800, h13001, h13009, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h13011 | h13011
                              · linarith only [h12796, h12800, h13007, h13011, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h1bigk with h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c | h13013c
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  linarith only [hlam, p13013_0]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  linarith only [h0, hlam, p13013_0]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  linarith only [h11385, hlam, p13013_0]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  rcases p13013_3 (m.d 0 1) (by simp) with h13017 | h13017
                                  · rcases p13013_3 (m.d 1 2) (by simp) with h13018 | h13018
                                    · rcases p13013_3 (m.d 1 3) (by simp) with h13019 | h13019
                                      · rcases p13013_3 (m.d 1 4) (by simp) with h13020 | h13020
                                        · linarith only [h13020, hlam, p13013_0]
                                        · rcases p13013_3 (m.d 1 5) (by simp) with h13022 | h13022
                                          · linarith only [h12795, h13022, hlam]
                                          · linarith only [h13005, h13022, hlam]
                                      · linarith only [h13003, h13019, hlam]
                                    · linarith only [h13001, h13018, hlam]
                                  · linarith only [h13017, hlam, p13013_0]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  rcases p13013_3 (m.d 0 1) (by simp) with h13028 | h13028
                                  · rcases p13013_3 (m.d 1 2) (by simp) with h13029 | h13029
                                    · rcases p13013_3 (m.d 1 3) (by simp) with h13030 | h13030
                                      · rcases p13013_3 (m.d 1 4) (by simp) with h13031 | h13031
                                        · linarith only [h12794, h13031, hlam]
                                        · rcases p13013_3 (m.d 1 5) (by simp) with h13033 | h13033
                                          · linarith only [h13033, hlam, p13013_0]
                                          · rcases h3bigk with h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c | h13035c
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [hlam, p13035_0]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [h11385, hlam, p13035_1]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [h11385, h13000, h13007, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13035_1]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              rcases p13035_3 (m.d 0 3) (by simp) with h13039 | h13039
                                              · rcases p13035_3 (m.d 1 3) (by simp) with h13040 | h13040
                                                · rcases p13035_3 (m.d 2 3) (by simp) with h13041 | h13041
                                                  · linarith only [h12796, h13041, hlam]
                                                  · linarith only [h13007, h13041, hlam]
                                                · linarith only [h13003, h13040, hlam]
                                              · linarith only [h13039, hlam, p13035_0]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              rcases p13035_3 (m.d 0 3) (by simp) with h13046 | h13046
                                              · rcases p13035_3 (m.d 1 3) (by simp) with h13047 | h13047
                                                · rcases p13035_3 (m.d 2 3) (by simp) with h13048 | h13048
                                                  · linarith only [h12796, h13048, hlam]
                                                  · linarith only [h13008, h13048, hlam]
                                                · linarith only [h13004, h13047, hlam]
                                              · linarith only [h13046, hlam, p13035_0]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [h11385, h13000, hc01, hc12, hlam, hphi, p13035_1]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [hlam, p13035_0]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [h13000, h13008, h13011, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13035_1]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              rcases p13035_3 (m.d 0 3) (by simp) with h13056 | h13056
                                              · linarith only [h11385, h13056, hlam]
                                              · linarith only [h12798, h13056, hlam]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              rcases p13035_3 (m.d 0 3) (by simp) with h13059 | h13059
                                              · linarith only [h11385, h13059, hlam]
                                              · linarith only [h12799, h13059, hlam]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [h12796, hlam, p13035_0]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [h13000, hlam, p13035_0]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [hlam, p13035_0]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [h0, h12796, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13035_1]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [h0, h12796, h13011, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13035_1]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [h12798, hlam, p13035_0]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [h13003, hlam, p13035_0]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [h13007, hlam, p13035_0]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [hlam, p13035_0]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [h13011, hlam, p13035_1]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [h12799, hlam, p13035_0]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [h13004, hlam, p13035_0]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [h13008, hlam, p13035_0]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [h12799, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p13035_1]
                                            · have p13035_0 := h13035c.1
                                              have p13035_1 := h13035c.2.1
                                              have p13035_2 := h13035c.2.2.1
                                              have p13035_3 := h13035c.2.2.2
                                              linarith only [hlam, p13035_0]
                                      · linarith only [h13004, h13030, hlam]
                                    · linarith only [h13002, h13029, hlam]
                                  · linarith only [h13028, hlam, p13013_0]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  rcases p13013_3 (m.d 0 1) (by simp) with h13080 | h13080
                                  · linarith only [h13080, hlam, p13013_0]
                                  · rcases p13013_3 (m.d 1 2) (by simp) with h13082 | h13082
                                    · rcases p13013_3 (m.d 1 3) (by simp) with h13083 | h13083
                                      · linarith only [h13000, h13083, hlam]
                                      · linarith only [h11385, h13083, hlam]
                                    · linarith only [h13082, hlam, p13013_0]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  linarith only [hlam, p13013_0]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  linarith only [h11385, hc01, hc12, hlam, hphi, p13013_1]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  rcases p13013_3 (m.d 0 1) (by simp) with h13089 | h13089
                                  · linarith only [h0, h13089, hlam]
                                  · linarith only [h12794, h13089, hlam]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  rcases p13013_3 (m.d 0 1) (by simp) with h13092 | h13092
                                  · linarith only [h0, h13092, hlam]
                                  · linarith only [h12795, h13092, hlam]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  rcases p13013_3 (m.d 0 1) (by simp) with h13095 | h13095
                                  · linarith only [h13095, hlam, p13013_0]
                                  · rcases p13013_3 (m.d 1 2) (by simp) with h13097 | h13097
                                    · rcases p13013_3 (m.d 1 3) (by simp) with h13098 | h13098
                                      · rcases p13013_3 (m.d 1 4) (by simp) with h13099 | h13099
                                        · linarith only [h13003, h13099, hlam]
                                        · rcases p13013_3 (m.d 1 5) (by simp) with h13101 | h13101
                                          · linarith only [h13004, h13101, hlam]
                                          · rcases h3bigk with h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c | h13103c
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [hlam, p13103_0]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [h11385, hlam, p13103_1]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [h12796, h13007, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p13103_1]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              rcases p13103_3 (m.d 0 3) (by simp) with h13107 | h13107
                                              · rcases p13103_3 (m.d 1 3) (by simp) with h13108 | h13108
                                                · rcases p13103_3 (m.d 2 3) (by simp) with h13109 | h13109
                                                  · linarith only [h12796, h13109, hlam]
                                                  · linarith only [h13007, h13109, hlam]
                                                · linarith only [h13003, h13108, hlam]
                                              · linarith only [h13107, hlam, p13103_0]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              rcases p13103_3 (m.d 0 3) (by simp) with h13114 | h13114
                                              · rcases p13103_3 (m.d 1 3) (by simp) with h13115 | h13115
                                                · rcases p13103_3 (m.d 2 3) (by simp) with h13116 | h13116
                                                  · linarith only [h12796, h13116, hlam]
                                                  · linarith only [h13008, h13116, hlam]
                                                · linarith only [h13004, h13115, hlam]
                                              · linarith only [h13114, hlam, p13103_0]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [h11385, h12795, h13001, h13005, h13007, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13103_1]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [hlam, p13103_0]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [h13000, h13008, h13011, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13103_1]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              rcases p13103_3 (m.d 0 3) (by simp) with h13124 | h13124
                                              · linarith only [h11385, h13124, hlam]
                                              · linarith only [h12798, h13124, hlam]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              rcases p13103_3 (m.d 0 3) (by simp) with h13127 | h13127
                                              · linarith only [h11385, h13127, hlam]
                                              · linarith only [h12799, h13127, hlam]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [h12796, hlam, p13103_0]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [h13000, hlam, p13103_0]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [hlam, p13103_0]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [h0, h12796, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13103_1]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [h0, h12796, h13011, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13103_1]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [h12798, hlam, p13103_0]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [h13003, hlam, p13103_0]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [h13007, hlam, p13103_0]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [hlam, p13103_0]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [h13011, hlam, p13103_1]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [h12799, hlam, p13103_0]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [h13004, hlam, p13103_0]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [h13008, hlam, p13103_0]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [h11385, h12799, h13000, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13103_1]
                                            · have p13103_0 := h13103c.1
                                              have p13103_1 := h13103c.2.1
                                              have p13103_2 := h13103c.2.2.1
                                              have p13103_3 := h13103c.2.2.2
                                              linarith only [hlam, p13103_0]
                                      · linarith only [h13098, hlam, p13013_0]
                                    · linarith only [h0, h13097, hlam]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  linarith only [h13000, hlam, p13013_1]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  linarith only [hlam, p13013_0]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  rcases p13013_3 (m.d 0 1) (by simp) with h13149 | h13149
                                  · linarith only [h11385, h13149, hlam]
                                  · linarith only [h12794, h13149, hlam]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  rcases p13013_3 (m.d 0 1) (by simp) with h13152 | h13152
                                  · linarith only [h11385, h13152, hlam]
                                  · linarith only [h12795, h13152, hlam]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  linarith only [h12794, hlam, p13013_0]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  linarith only [h13001, hlam, p13013_1]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  linarith only [h13003, hlam, p13013_0]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  linarith only [hlam, p13013_0]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  linarith only [h13005, hlam, p13013_1]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  linarith only [h12795, hlam, p13013_0]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  linarith only [h13002, hlam, p13013_1]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  linarith only [h13004, hlam, p13013_0]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  linarith only [h0, h12795, h13001, h13007, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13013_1]
                                · have p13013_0 := h13013c.1
                                  have p13013_1 := h13013c.2.1
                                  have p13013_2 := h13013c.2.2.1
                                  have p13013_3 := h13013c.2.2.2
                                  linarith only [hlam, p13013_0]
                          · linarith only [h11385, h12795, h13000, h13004, h13007, h13008, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13166 | h13166
                          · linarith only [h11385, h12794, h13000, h13003, h13007, h13166, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13168 | h13168
                            · linarith only [h11385, h12795, h12800, h13000, h13003, h13005, h13007, h13168, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h13170 | h13170
                              · linarith only [h12794, h12800, h13003, h13170, hlam]
                              · rcases h1bigk with h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c | h13172c
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [hlam, p13172_0]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [h0, hlam, p13172_0]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [h11385, hlam, p13172_0]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [h11385, h13000, h13003, h13007, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13172_1]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [h11385, h13000, h13004, h13007, h13170, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13172_1]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [h12794, h13003, h13007, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13172_1]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [hlam, p13172_0]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [h11385, hc01, hc12, hlam, hphi, p13172_1]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  rcases p13172_3 (m.d 0 1) (by simp) with h13181 | h13181
                                  · linarith only [h0, h13181, hlam]
                                  · linarith only [h12794, h13181, hlam]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  rcases p13172_3 (m.d 0 1) (by simp) with h13184 | h13184
                                  · linarith only [h0, h13184, hlam]
                                  · linarith only [h12795, h13184, hlam]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [h12795, h13004, h13007, h13170, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13172_1]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [h13000, hlam, p13172_1]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [hlam, p13172_0]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  rcases p13172_3 (m.d 0 1) (by simp) with h13190 | h13190
                                  · linarith only [h11385, h13190, hlam]
                                  · linarith only [h12794, h13190, hlam]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  rcases p13172_3 (m.d 0 1) (by simp) with h13193 | h13193
                                  · linarith only [h11385, h13193, hlam]
                                  · linarith only [h12795, h13193, hlam]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [h12794, hlam, p13172_0]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [h13001, hlam, p13172_1]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [h13003, hlam, p13172_0]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [hlam, p13172_0]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [h13005, hlam, p13172_1]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [h12795, hlam, p13172_0]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [h13002, hlam, p13172_1]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [h13004, hlam, p13172_0]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [h12795, h13003, h13007, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13172_1]
                                · have p13172_0 := h13172c.1
                                  have p13172_1 := h13172c.2.1
                                  have p13172_2 := h13172c.2.2.1
                                  have p13172_3 := h13172c.2.2.2
                                  linarith only [hlam, p13172_0]
                    · linarith only [h11385, h12799, h13004, hlam]
                  · linarith only [h11385, h12798, h13003, hlam]
                · linarith only [h0, h12795, h13002, hlam]
              · linarith only [h0, h12797, h13001, hlam]
            · linarith only [h0, h12796, h13000, hlam]
        · linarith only [h11385, h12795, h12799, hlam]
      · linarith only [h11385, h12794, h12798, hlam]
    · linarith only [h11385, h12794, h12796, h12797, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h13214 | h13214
    · rcases m.htr 0 3 4 (by decide) (by decide) with h13215 | h13215
      · rcases m.htr 0 3 5 (by decide) (by decide) with h13216 | h13216
        · rcases m.htr 0 4 5 (by decide) (by decide) with h13217 | h13217
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13218 | h13218
            · rcases m.htr 1 2 4 (by decide) (by decide) with h13219 | h13219
              · rcases m.htr 1 2 5 (by decide) (by decide) with h13220 | h13220
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13221 | h13221
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h13222 | h13222
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13223 | h13223
                      · linarith only [h0, h12794, h12796, h13218, h13223, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h12794, h12796, h13217, h13218, h13223, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h12795, h12796, h13216, h13218, h13222, hc03, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h11385, h13215, h13221, hlam]
                · linarith only [h0, h12794, h12796, h13218, h13219, h13220, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h0, h12794, h12796, h13218, h13219, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h13230 | h13230
              · rcases m.htr 1 2 5 (by decide) (by decide) with h13231 | h13231
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13232 | h13232
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h13233 | h13233
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13234 | h13234
                      · linarith only [h0, h12794, h13218, h13234, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h12794, h13217, h13218, h13234, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h11385, h13216, h13233, hlam]
                  · linarith only [h11385, h13215, h13232, hlam]
                · linarith only [h0, h12795, h13231, hlam]
              · linarith only [h0, h12795, h13214, h13230, hc02, hc15, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13241 | h13241
            · rcases m.htr 1 2 4 (by decide) (by decide) with h13242 | h13242
              · rcases m.htr 1 2 5 (by decide) (by decide) with h13243 | h13243
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13244 | h13244
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h13245 | h13245
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13246 | h13246
                      · linarith only [h0, h12794, h13217, h13246, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h13248 | h13248
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13249 | h13249
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13250 | h13250
                            · linarith only [h12796, h13214, h13217, h13241, h13250, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h13252 | h13252
                              · linarith only [h0, h12794, h12796, h13217, h13241, h13242, h13248, h13252, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases h1bigk with h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c | h13254c
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [hlam, p13254_0]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [h0, hlam, p13254_0]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [h11385, hlam, p13254_0]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [h0, h12796, h13241, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p13254_1]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [h0, h12796, h13241, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p13254_1]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  rcases p13254_3 (m.d 0 1) (by simp) with h13260 | h13260
                                  · linarith only [h13260, hlam, p13254_0]
                                  · rcases p13254_3 (m.d 1 2) (by simp) with h13262 | h13262
                                    · rcases p13254_3 (m.d 1 3) (by simp) with h13263 | h13263
                                      · linarith only [h13241, h13263, hlam]
                                      · linarith only [h11385, h13263, hlam]
                                    · linarith only [h13262, hlam, p13254_0]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [hlam, p13254_0]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [h11385, hc01, hc12, hlam, hphi, p13254_1]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [h0, h12795, h12796, h13241, h13246, hlam, p13254_2]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [h0, h12795, h12796, h13241, hlam, p13254_2]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  rcases p13254_3 (m.d 0 1) (by simp) with h13271 | h13271
                                  · linarith only [h13271, hlam, p13254_0]
                                  · rcases p13254_3 (m.d 1 2) (by simp) with h13273 | h13273
                                    · rcases p13254_3 (m.d 1 3) (by simp) with h13274 | h13274
                                      · rcases p13254_3 (m.d 1 4) (by simp) with h13275 | h13275
                                        · linarith only [h13244, h13275, hlam]
                                        · rcases p13254_3 (m.d 1 5) (by simp) with h13277 | h13277
                                          · linarith only [h13245, h13277, hlam]
                                          · rcases h3bigk with h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c | h13279c
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [hlam, p13279_0]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h11385, hlam, p13279_1]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h12796, hlam, p13279_1]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h12796, h13241, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13279_1]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h12796, h13241, h13252, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13279_1]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h11385, h12795, h13242, h13246, h13248, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13279_1]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [hlam, p13279_0]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h0, h12795, h12796, h13241, h13242, h13246, h13248, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13279_1]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              rcases p13279_3 (m.d 0 3) (by simp) with h13288 | h13288
                                              · linarith only [h11385, h13288, hlam]
                                              · linarith only [h13215, h13288, hlam]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              rcases p13279_3 (m.d 0 3) (by simp) with h13291 | h13291
                                              · linarith only [h11385, h13291, hlam]
                                              · linarith only [h13216, h13291, hlam]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h0, h12795, h12796, h13242, h13246, h13248, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13279_1]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h13241, hlam, p13279_0]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [hlam, p13279_0]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h13241, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13279_1]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h13241, h13252, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13279_1]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h13215, hlam, p13279_0]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h13244, hlam, p13279_0]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h13248, hlam, p13279_0]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [hlam, p13279_0]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h13252, hlam, p13279_1]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h13216, hlam, p13279_0]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h13245, hlam, p13279_0]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h13249, hlam, p13279_0]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [h13216, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p13279_1]
                                            · have p13279_0 := h13279c.1
                                              have p13279_1 := h13279c.2.1
                                              have p13279_2 := h13279c.2.2.1
                                              have p13279_3 := h13279c.2.2.2
                                              linarith only [hlam, p13279_0]
                                      · linarith only [h13274, hlam, p13254_0]
                                    · linarith only [h0, h13273, hlam]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [h13241, hlam, p13254_1]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [hlam, p13254_0]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  rcases p13254_3 (m.d 0 1) (by simp) with h13313 | h13313
                                  · linarith only [h11385, h13313, hlam]
                                  · linarith only [h12794, h13313, hlam]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  rcases p13254_3 (m.d 0 1) (by simp) with h13316 | h13316
                                  · linarith only [h11385, h13316, hlam]
                                  · linarith only [h12795, h13316, hlam]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [h12794, hlam, p13254_0]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [h13242, hlam, p13254_1]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [h13244, hlam, p13254_0]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [hlam, p13254_0]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [h13246, hlam, p13254_1]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [h12795, hlam, p13254_0]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [h13243, hlam, p13254_1]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [h13245, hlam, p13254_0]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [h0, h12795, h12796, h13241, h13242, h13248, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13254_1]
                                · have p13254_0 := h13254c.1
                                  have p13254_1 := h13254c.2.1
                                  have p13254_2 := h13254c.2.2.1
                                  have p13254_3 := h13254c.2.2.2
                                  linarith only [hlam, p13254_0]
                          · linarith only [h12796, h13216, h13249, hlam]
                        · linarith only [h12796, h13215, h13248, hlam]
                    · linarith only [h12796, h13216, h13241, h13245, hlam]
                  · linarith only [h12796, h13215, h13241, h13244, hlam]
                · linarith only [h0, h12796, h13241, h13243, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h12794, h12796, h13241, h13242, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h13335 | h13335
              · rcases m.htr 1 2 5 (by decide) (by decide) with h13336 | h13336
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13337 | h13337
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h13338 | h13338
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13339 | h13339
                      · linarith only [h0, h12794, h13217, h13339, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h13341 | h13341
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13342 | h13342
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13343 | h13343
                            · linarith only [h12794, h13217, h13335, h13343, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h13345 | h13345
                              · linarith only [h12794, h13217, h13335, h13341, h13345, hlam]
                              · rcases h1bigk with h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c | h13347c
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [hlam, p13347_0]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [h0, hlam, p13347_0]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [h11385, hlam, p13347_0]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [h0, h13241, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13347_1]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [h0, h13241, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p13347_1]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [h13241, hc01, hc23, hlam, hphi, ht12, p13347_1]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [hlam, p13347_0]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [h13241, hlam, p13347_0]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  rcases p13347_3 (m.d 0 1) (by simp) with h13356 | h13356
                                  · linarith only [h0, h13356, hlam]
                                  · linarith only [h12794, h13356, hlam]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  rcases p13347_3 (m.d 0 1) (by simp) with h13359 | h13359
                                  · linarith only [h0, h13359, hlam]
                                  · linarith only [h12795, h13359, hlam]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  rcases p13347_3 (m.d 0 1) (by simp) with h13362 | h13362
                                  · linarith only [h13362, hlam, p13347_0]
                                  · rcases p13347_3 (m.d 1 2) (by simp) with h13364 | h13364
                                    · linarith only [h13241, h13364, hlam]
                                    · linarith only [h0, h13364, hlam]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [h0, h12795, h13241, h13335, h13339, h13341, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13347_1]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [hlam, p13347_0]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  rcases p13347_3 (m.d 0 1) (by simp) with h13369 | h13369
                                  · linarith only [h11385, h13369, hlam]
                                  · linarith only [h12794, h13369, hlam]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  rcases p13347_3 (m.d 0 1) (by simp) with h13372 | h13372
                                  · linarith only [h11385, h13372, hlam]
                                  · linarith only [h12795, h13372, hlam]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [h12794, hlam, p13347_0]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [h13335, hlam, p13347_1]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [h13337, hlam, p13347_0]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [hlam, p13347_0]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [h13339, hlam, p13347_1]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [h12795, hlam, p13347_0]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [h13336, hlam, p13347_1]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [h13338, hlam, p13347_0]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [h0, h12795, h13335, h13341, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13347_1]
                                · have p13347_0 := h13347c.1
                                  have p13347_1 := h13347c.2.1
                                  have p13347_2 := h13347c.2.2.1
                                  have p13347_3 := h13347c.2.2.2
                                  linarith only [hlam, p13347_0]
                          · linarith only [h0, h13241, h13342, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h12795, h13241, h13335, h13339, h13341, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h11385, h13216, h13338, hlam]
                  · linarith only [h11385, h13215, h13337, hlam]
                · linarith only [h0, h12795, h13336, hlam]
              · linarith only [h0, h13214, h13335, hlam]
        · linarith only [h0, h12795, h12796, h13216, hlam]
      · linarith only [h0, h12794, h12796, h13215, hlam]
    · linarith only [h0, h12794, h13214, hlam]

end R2N4
