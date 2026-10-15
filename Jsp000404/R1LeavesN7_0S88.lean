import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x10 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h37309 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h37310 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h37311 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h37312 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h37313 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h37314 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h37316 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h37317 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h37318 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h37320 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h37322c : ((m.d 1 3) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 3) ∧ (m.d 0 1) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 0 1) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have p37322_0 := h37322c.1
  have p37322_1 := h37322c.2.1
  have p37322_2 := h37322c.2.2.1
  have p37322_3 := h37322c.2.2.2
  rcases p37322_3 (m.d 0 1) (by simp) with h37770 | h37770
  · linarith only [h37770, hlam, p37322_0]
  · rcases p37322_3 (m.d 1 2) (by simp) with h37772 | h37772
    · rcases p37322_3 (m.d 1 3) (by simp) with h37773 | h37773
      · rcases p37322_3 (m.d 1 4) (by simp) with h37774 | h37774
        · linarith only [h37312, h37774, hlam]
        · rcases p37322_3 (m.d 1 5) (by simp) with h37776 | h37776
          · linarith only [h37313, h37776, hlam]
          · rcases h1emax with h37778 | h37778 | h37778 | h37778 | h37778
            · rcases h2bigk with h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c | h37779c
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [hlam, p37779_0]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [h0, hlam, p37779_0]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                rcases p37779_3 (m.d 0 2) (by simp) with h37782 | h37782
                · rcases p37779_3 (m.d 1 2) (by simp) with h37783 | h37783
                  · rcases p37779_3 (m.d 2 3) (by simp) with h37784 | h37784
                    · linarith only [h37784, hlam, p37779_0]
                    · rcases p37779_3 (m.d 2 4) (by simp) with h37786 | h37786
                      · linarith only [h36831, h37786, hlam]
                      · rcases p37779_3 (m.d 2 5) (by simp) with h37788 | h37788
                        · linarith only [h36832, h37788, hlam]
                        · rcases h4bigk with h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c | h37790c
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [hlam, p37790_0]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [h36828, h37310, h37316, h37778, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37790_1]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [h36829, h36835, h37309, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37790_1]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [h36829, h36835, h37309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37790_1]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [h36835, hlam, p37790_0]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [h36828, hlam, p37790_0]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [hlam, p37790_0]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [h36828, h37309, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37790_1]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [h36829, h37309, h37314, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37790_1]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [h37314, hlam, p37790_0]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [h36831, hlam, p37790_0]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [h37310, hlam, p37790_0]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [hlam, p37790_0]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [h36829, h36831, h36835, h37309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37790_1]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [h37318, hlam, p37790_0]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [h36833, hlam, p37790_0]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [h37312, hlam, p37790_0]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [h37316, hlam, p37790_0]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [hlam, p37790_0]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [h37320, hlam, p37790_0]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            rcases p37790_3 (m.d 0 4) (by simp) with h37811 | h37811
                            · linarith only [h37811, hlam, p37790_0]
                            · rcases p37790_3 (m.d 1 4) (by simp) with h37813 | h37813
                              · linarith only [h37314, h37813, hlam]
                              · rcases p37790_3 (m.d 2 4) (by simp) with h37815 | h37815
                                · linarith only [h37318, h37815, hlam]
                                · rcases p37790_3 (m.d 3 4) (by simp) with h37817 | h37817
                                  · linarith only [h37320, h37817, hlam]
                                  · rcases p37790_3 (m.d 4 5) (by simp) with h37819 | h37819
                                    · rcases h5bigk with h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c | h37820c
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [hlam, p37820_0]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h36829, h37309, h37314, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37820_1]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h36829, h37309, h37317, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37820_1]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h36829, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37820_1]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h36835, hlam, p37820_0]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h36829, hlam, p37820_0]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [hlam, p37820_0]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h36829, h37309, h37317, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37820_1]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h36829, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37820_1]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h37314, hlam, p37820_0]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h36832, hlam, p37820_1]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h37311, hlam, p37820_1]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [hlam, p37820_0]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h0, h36832, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37820_1]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h37318, hlam, p37820_0]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h36834, hlam, p37820_1]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h37313, hlam, p37820_1]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h37317, hlam, p37820_0]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [hlam, p37820_0]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h37320, hlam, p37820_0]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h36834, h37320, hc34, hc45, hlam, hphi, p37820_1]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h37313, h37320, hc34, hc45, hlam, hphi, p37820_1]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h37317, h37320, hc34, hc45, hlam, hphi, p37820_1]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [h37320, hc34, hc45, hlam, hphi, p37820_1]
                                      · have p37820_0 := h37820c.1
                                        have p37820_1 := h37820c.2.1
                                        have p37820_2 := h37820c.2.2.1
                                        have p37820_3 := h37820c.2.2.2
                                        linarith only [hlam, p37820_0]
                                    · linarith only [h37819, hlam, p37790_0]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            rcases p37790_3 (m.d 0 4) (by simp) with h37847 | h37847
                            · linarith only [h36835, h37847, hlam]
                            · linarith only [h36828, h37847, hlam]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            rcases p37790_3 (m.d 0 4) (by simp) with h37850 | h37850
                            · linarith only [h36835, h37850, hlam]
                            · linarith only [h36831, h37850, hlam]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            rcases p37790_3 (m.d 0 4) (by simp) with h37853 | h37853
                            · linarith only [h36835, h37853, hlam]
                            · linarith only [h36833, h37853, hlam]
                          · have p37790_0 := h37790c.1
                            have p37790_1 := h37790c.2.1
                            have p37790_2 := h37790c.2.2.1
                            have p37790_3 := h37790c.2.2.2
                            linarith only [hlam, p37790_0]
                  · linarith only [h37309, h37783, hlam]
                · linarith only [h37782, hlam, p37779_0]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                rcases p37779_3 (m.d 0 2) (by simp) with h37859 | h37859
                · rcases p37779_3 (m.d 1 2) (by simp) with h37860 | h37860
                  · rcases p37779_3 (m.d 2 3) (by simp) with h37861 | h37861
                    · linarith only [h36830, h37861, hlam]
                    · linarith only [h37316, h37861, hlam]
                  · linarith only [h37310, h37860, hlam]
                · linarith only [h37859, hlam, p37779_0]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                rcases p37779_3 (m.d 0 2) (by simp) with h37866 | h37866
                · rcases p37779_3 (m.d 1 2) (by simp) with h37867 | h37867
                  · rcases p37779_3 (m.d 2 3) (by simp) with h37868 | h37868
                    · linarith only [h36830, h37868, hlam]
                    · linarith only [h37317, h37868, hlam]
                  · linarith only [h37311, h37867, hlam]
                · linarith only [h37866, hlam, p37779_0]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [h36830, h37317, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37779_1]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [hlam, p37779_0]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                rcases p37779_3 (m.d 0 2) (by simp) with h37875 | h37875
                · linarith only [h0, h37875, hlam]
                · linarith only [h36830, h37875, hlam]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [h36828, h37309, h37310, hlam, p37322_1, p37779_2]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [h36829, h37309, h37311, hlam, p37322_1, p37779_2]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [h36830, hlam, p37779_0]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [h37309, hlam, p37779_0]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [hlam, p37779_0]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                rcases p37779_3 (m.d 0 2) (by simp) with h37883 | h37883
                · rcases p37779_3 (m.d 1 2) (by simp) with h37884 | h37884
                  · rcases p37779_3 (m.d 2 3) (by simp) with h37885 | h37885
                    · rcases p37779_3 (m.d 2 4) (by simp) with h37886 | h37886
                      · linarith only [h37316, h37886, hlam]
                      · rcases p37779_3 (m.d 2 5) (by simp) with h37888 | h37888
                        · linarith only [h37317, h37888, hlam]
                        · linarith only [h37318, h37888, hlam]
                    · linarith only [h37316, h37885, hlam]
                  · linarith only [h37310, h37884, hlam]
                · linarith only [h36831, h37883, hlam]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                rcases p37779_3 (m.d 0 2) (by simp) with h37894 | h37894
                · rcases p37779_3 (m.d 1 2) (by simp) with h37895 | h37895
                  · rcases p37779_3 (m.d 2 3) (by simp) with h37896 | h37896
                    · rcases p37779_3 (m.d 2 4) (by simp) with h37897 | h37897
                      · linarith only [h37316, h37897, hlam]
                      · rcases p37779_3 (m.d 2 5) (by simp) with h37899 | h37899
                        · linarith only [h37317, h37899, hlam]
                        · rcases h4bigk with h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c | h37901c
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [hlam, p37901_0]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [h36828, h37310, h37316, h37778, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37901_1]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [h36828, h37309, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37901_1]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [h36828, h37309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37901_1]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [h36835, hlam, p37901_0]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [h36828, hlam, p37901_0]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [hlam, p37901_0]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [h36828, h37309, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37901_1]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [h36829, h37309, h37314, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37901_1]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [h37314, hlam, p37901_0]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [h36831, hlam, p37901_0]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [h37310, hlam, p37901_0]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [hlam, p37901_0]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [h36829, h36831, h36835, h37309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37901_1]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [h37318, hlam, p37901_0]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [h36833, hlam, p37901_0]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [h37312, hlam, p37901_0]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [h37316, hlam, p37901_0]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [hlam, p37901_0]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [h37320, hlam, p37901_0]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            rcases p37901_3 (m.d 0 4) (by simp) with h37922 | h37922
                            · linarith only [h37922, hlam, p37901_0]
                            · rcases p37901_3 (m.d 1 4) (by simp) with h37924 | h37924
                              · linarith only [h37314, h37924, hlam]
                              · rcases p37901_3 (m.d 2 4) (by simp) with h37926 | h37926
                                · linarith only [h37318, h37926, hlam]
                                · rcases p37901_3 (m.d 3 4) (by simp) with h37928 | h37928
                                  · linarith only [h37320, h37928, hlam]
                                  · rcases p37901_3 (m.d 4 5) (by simp) with h37930 | h37930
                                    · rcases h5bigk with h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c | h37931c
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [hlam, p37931_0]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h36829, h37309, h37314, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37931_1]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h36829, h37309, h37317, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37931_1]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h36829, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37931_1]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h36835, hlam, p37931_0]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h36829, hlam, p37931_0]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [hlam, p37931_0]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h36829, h37309, h37317, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37931_1]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h36829, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37931_1]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h37314, hlam, p37931_0]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h36832, hlam, p37931_1]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h37311, hlam, p37931_1]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [hlam, p37931_0]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h36830, h37320, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p37779_1, p37931_1]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h37318, hlam, p37931_0]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h36834, hlam, p37931_1]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h37313, hlam, p37931_1]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h37317, hlam, p37931_0]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [hlam, p37931_0]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h37320, hlam, p37931_0]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h36834, h37320, hc34, hc45, hlam, hphi, p37931_1]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h37313, h37320, hc34, hc45, hlam, hphi, p37931_1]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h37317, h37320, hc34, hc45, hlam, hphi, p37931_1]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [h37320, hc34, hc45, hlam, hphi, p37931_1]
                                      · have p37931_0 := h37931c.1
                                        have p37931_1 := h37931c.2.1
                                        have p37931_2 := h37931c.2.2.1
                                        have p37931_3 := h37931c.2.2.2
                                        linarith only [hlam, p37931_0]
                                    · linarith only [h37930, hlam, p37901_0]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            rcases p37901_3 (m.d 0 4) (by simp) with h37958 | h37958
                            · linarith only [h36835, h37958, hlam]
                            · linarith only [h36828, h37958, hlam]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            rcases p37901_3 (m.d 0 4) (by simp) with h37961 | h37961
                            · linarith only [h36835, h37961, hlam]
                            · linarith only [h36831, h37961, hlam]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            rcases p37901_3 (m.d 0 4) (by simp) with h37964 | h37964
                            · linarith only [h36835, h37964, hlam]
                            · linarith only [h36833, h37964, hlam]
                          · have p37901_0 := h37901c.1
                            have p37901_1 := h37901c.2.1
                            have p37901_2 := h37901c.2.2.1
                            have p37901_3 := h37901c.2.2.2
                            linarith only [hlam, p37901_0]
                    · linarith only [h37317, h37896, hlam]
                  · linarith only [h37311, h37895, hlam]
                · linarith only [h36832, h37894, hlam]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [h36831, hlam, p37779_0]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [h37310, hlam, p37779_0]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [h37316, hlam, p37779_0]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [hlam, p37779_0]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [h37318, hlam, p37779_0]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [h36832, hlam, p37779_0]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [h37311, hlam, p37779_0]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [h37317, hlam, p37779_0]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [h36829, h36832, h37309, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37779_1]
              · have p37779_0 := h37779c.1
                have p37779_1 := h37779c.2.1
                have p37779_2 := h37779c.2.2.1
                have p37779_3 := h37779c.2.2.2
                linarith only [hlam, p37779_0]
            · linarith only [h37309, h37778, hc01, hlam, p37322_1]
            · linarith only [h36829, h37310, h37314, h37316, h37778, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1]
            · rcases h2bigk with h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c | h37983c
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [hlam, p37983_0]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [h0, hlam, p37983_0]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                rcases p37983_3 (m.d 0 2) (by simp) with h37986 | h37986
                · rcases p37983_3 (m.d 1 2) (by simp) with h37987 | h37987
                  · rcases p37983_3 (m.d 2 3) (by simp) with h37988 | h37988
                    · linarith only [h37988, hlam, p37983_0]
                    · rcases p37983_3 (m.d 2 4) (by simp) with h37990 | h37990
                      · linarith only [h36831, h37990, hlam]
                      · rcases p37983_3 (m.d 2 5) (by simp) with h37992 | h37992
                        · linarith only [h36832, h37992, hlam]
                        · rcases h4bigk with h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c | h37994c
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [hlam, p37994_0]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [h36828, h37309, h37310, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37994_1]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [h36828, h37309, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37994_1]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [h36828, h37309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37994_1]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [h36835, hlam, p37994_0]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [h36828, hlam, p37994_0]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [hlam, p37994_0]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [h36828, h37309, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37994_1]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [h36829, h37309, h37314, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37994_1]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [h37314, hlam, p37994_0]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [h36831, hlam, p37994_0]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [h37310, hlam, p37994_0]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [hlam, p37994_0]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [h36829, h36831, h36835, h37309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37994_1]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [h37318, hlam, p37994_0]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [h36833, hlam, p37994_0]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [h37312, hlam, p37994_0]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [h37316, hlam, p37994_0]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [hlam, p37994_0]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [h37320, hlam, p37994_0]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            rcases p37994_3 (m.d 0 4) (by simp) with h38015 | h38015
                            · linarith only [h38015, hlam, p37994_0]
                            · rcases p37994_3 (m.d 1 4) (by simp) with h38017 | h38017
                              · linarith only [h37314, h38017, hlam]
                              · rcases p37994_3 (m.d 2 4) (by simp) with h38019 | h38019
                                · linarith only [h37318, h38019, hlam]
                                · rcases p37994_3 (m.d 3 4) (by simp) with h38021 | h38021
                                  · linarith only [h37320, h38021, hlam]
                                  · rcases p37994_3 (m.d 4 5) (by simp) with h38023 | h38023
                                    · rcases h5bigk with h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c | h38024c
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [hlam, p38024_0]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h36829, h37309, h37314, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38024_1]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h36829, h37309, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p37322_1, p38024_1]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h36829, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38024_1]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h36835, hlam, p38024_0]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h36829, hlam, p38024_0]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [hlam, p38024_0]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h36829, h37309, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p37322_1, p38024_1]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h36829, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38024_1]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h37314, hlam, p38024_0]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h36832, hlam, p38024_1]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h37311, hlam, p38024_1]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [hlam, p38024_0]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h0, h36832, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38024_1]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h37318, hlam, p38024_0]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h36834, hlam, p38024_1]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h37313, hlam, p38024_1]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h37317, hlam, p38024_0]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [hlam, p38024_0]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h37320, hlam, p38024_0]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h36834, h37320, hc34, hc45, hlam, hphi, p38024_1]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h37313, h37320, hc34, hc45, hlam, hphi, p38024_1]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h37317, h37320, hc34, hc45, hlam, hphi, p38024_1]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [h37320, hc34, hc45, hlam, hphi, p38024_1]
                                      · have p38024_0 := h38024c.1
                                        have p38024_1 := h38024c.2.1
                                        have p38024_2 := h38024c.2.2.1
                                        have p38024_3 := h38024c.2.2.2
                                        linarith only [hlam, p38024_0]
                                    · linarith only [h38023, hlam, p37994_0]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            rcases p37994_3 (m.d 0 4) (by simp) with h38051 | h38051
                            · linarith only [h36835, h38051, hlam]
                            · linarith only [h36828, h38051, hlam]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            rcases p37994_3 (m.d 0 4) (by simp) with h38054 | h38054
                            · linarith only [h36835, h38054, hlam]
                            · linarith only [h36831, h38054, hlam]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            rcases p37994_3 (m.d 0 4) (by simp) with h38057 | h38057
                            · linarith only [h36835, h38057, hlam]
                            · linarith only [h36833, h38057, hlam]
                          · have p37994_0 := h37994c.1
                            have p37994_1 := h37994c.2.1
                            have p37994_2 := h37994c.2.2.1
                            have p37994_3 := h37994c.2.2.2
                            linarith only [hlam, p37994_0]
                  · linarith only [h37309, h37987, hlam]
                · linarith only [h37986, hlam, p37983_0]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                rcases p37983_3 (m.d 0 2) (by simp) with h38063 | h38063
                · rcases p37983_3 (m.d 1 2) (by simp) with h38064 | h38064
                  · rcases p37983_3 (m.d 2 3) (by simp) with h38065 | h38065
                    · linarith only [h36830, h38065, hlam]
                    · linarith only [h37316, h38065, hlam]
                  · linarith only [h37310, h38064, hlam]
                · linarith only [h38063, hlam, p37983_0]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                rcases p37983_3 (m.d 0 2) (by simp) with h38070 | h38070
                · rcases p37983_3 (m.d 1 2) (by simp) with h38071 | h38071
                  · rcases p37983_3 (m.d 2 3) (by simp) with h38072 | h38072
                    · linarith only [h36830, h38072, hlam]
                    · linarith only [h37317, h38072, hlam]
                  · linarith only [h37311, h38071, hlam]
                · linarith only [h38070, hlam, p37983_0]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [h36830, h37317, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37983_1]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [hlam, p37983_0]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                rcases p37983_3 (m.d 0 2) (by simp) with h38079 | h38079
                · linarith only [h0, h38079, hlam]
                · linarith only [h36830, h38079, hlam]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [h36828, h37309, h37310, hlam, p37322_1, p37983_2]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [h36829, h37309, h37311, hlam, p37322_1, p37983_2]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [h36830, hlam, p37983_0]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [h37309, hlam, p37983_0]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [hlam, p37983_0]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                rcases p37983_3 (m.d 0 2) (by simp) with h38087 | h38087
                · rcases p37983_3 (m.d 1 2) (by simp) with h38088 | h38088
                  · rcases p37983_3 (m.d 2 3) (by simp) with h38089 | h38089
                    · rcases p37983_3 (m.d 2 4) (by simp) with h38090 | h38090
                      · linarith only [h37316, h38090, hlam]
                      · rcases p37983_3 (m.d 2 5) (by simp) with h38092 | h38092
                        · linarith only [h37317, h38092, hlam]
                        · linarith only [h37318, h38092, hlam]
                    · linarith only [h37316, h38089, hlam]
                  · linarith only [h37310, h38088, hlam]
                · linarith only [h36831, h38087, hlam]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                rcases p37983_3 (m.d 0 2) (by simp) with h38098 | h38098
                · rcases p37983_3 (m.d 1 2) (by simp) with h38099 | h38099
                  · rcases p37983_3 (m.d 2 3) (by simp) with h38100 | h38100
                    · rcases p37983_3 (m.d 2 4) (by simp) with h38101 | h38101
                      · linarith only [h37316, h38101, hlam]
                      · rcases p37983_3 (m.d 2 5) (by simp) with h38103 | h38103
                        · linarith only [h37317, h38103, hlam]
                        · rcases h4bigk with h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c | h38105c
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [hlam, p38105_0]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [h36828, h37309, h37310, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38105_1]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [h36828, h37309, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38105_1]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [h36828, h37309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38105_1]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [h36835, hlam, p38105_0]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [h36828, hlam, p38105_0]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [hlam, p38105_0]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [h36828, h37309, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38105_1]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [h36829, h37309, h37314, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38105_1]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [h37314, hlam, p38105_0]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [h36831, hlam, p38105_0]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [h37310, hlam, p38105_0]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [hlam, p38105_0]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [h36828, h36831, h37309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38105_1]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [h37318, hlam, p38105_0]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [h36833, hlam, p38105_0]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [h37312, hlam, p38105_0]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [h37316, hlam, p38105_0]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [hlam, p38105_0]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [h37320, hlam, p38105_0]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            rcases p38105_3 (m.d 0 4) (by simp) with h38126 | h38126
                            · linarith only [h38126, hlam, p38105_0]
                            · rcases p38105_3 (m.d 1 4) (by simp) with h38128 | h38128
                              · linarith only [h37314, h38128, hlam]
                              · rcases p38105_3 (m.d 2 4) (by simp) with h38130 | h38130
                                · linarith only [h37318, h38130, hlam]
                                · rcases p38105_3 (m.d 3 4) (by simp) with h38132 | h38132
                                  · linarith only [h37320, h38132, hlam]
                                  · rcases p38105_3 (m.d 4 5) (by simp) with h38134 | h38134
                                    · rcases h5bigk with h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c | h38135c
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [hlam, p38135_0]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h36829, h37309, h37314, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38135_1]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h36829, h37309, h37317, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38135_1]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h36829, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38135_1]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h36835, hlam, p38135_0]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h36829, hlam, p38135_0]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [hlam, p38135_0]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h36829, h37309, h37317, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38135_1]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h36829, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38135_1]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h37314, hlam, p38135_0]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h36832, hlam, p38135_1]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h37311, hlam, p38135_1]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [hlam, p38135_0]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h36830, h37320, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p37983_1, p38135_1]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h37318, hlam, p38135_0]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h36834, hlam, p38135_1]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h37313, hlam, p38135_1]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h37317, hlam, p38135_0]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [hlam, p38135_0]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h37320, hlam, p38135_0]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h36834, h37320, hc34, hc45, hlam, hphi, p38135_1]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h37313, h37320, hc34, hc45, hlam, hphi, p38135_1]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h37317, h37320, hc34, hc45, hlam, hphi, p38135_1]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [h37320, hc34, hc45, hlam, hphi, p38135_1]
                                      · have p38135_0 := h38135c.1
                                        have p38135_1 := h38135c.2.1
                                        have p38135_2 := h38135c.2.2.1
                                        have p38135_3 := h38135c.2.2.2
                                        linarith only [hlam, p38135_0]
                                    · linarith only [h38134, hlam, p38105_0]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            rcases p38105_3 (m.d 0 4) (by simp) with h38162 | h38162
                            · linarith only [h36835, h38162, hlam]
                            · linarith only [h36828, h38162, hlam]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            rcases p38105_3 (m.d 0 4) (by simp) with h38165 | h38165
                            · linarith only [h36835, h38165, hlam]
                            · linarith only [h36831, h38165, hlam]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            rcases p38105_3 (m.d 0 4) (by simp) with h38168 | h38168
                            · linarith only [h36835, h38168, hlam]
                            · linarith only [h36833, h38168, hlam]
                          · have p38105_0 := h38105c.1
                            have p38105_1 := h38105c.2.1
                            have p38105_2 := h38105c.2.2.1
                            have p38105_3 := h38105c.2.2.2
                            linarith only [hlam, p38105_0]
                    · linarith only [h37317, h38100, hlam]
                  · linarith only [h37311, h38099, hlam]
                · linarith only [h36832, h38098, hlam]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [h36831, hlam, p37983_0]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [h37310, hlam, p37983_0]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [h37316, hlam, p37983_0]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [hlam, p37983_0]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [h37318, hlam, p37983_0]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [h36832, hlam, p37983_0]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [h37311, hlam, p37983_0]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [h37317, hlam, p37983_0]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [h36829, h36832, h37309, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37983_1]
              · have p37983_0 := h37983c.1
                have p37983_1 := h37983c.2.1
                have p37983_2 := h37983c.2.2.1
                have p37983_3 := h37983c.2.2.2
                linarith only [hlam, p37983_0]
            · rcases h2bigk with h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c | h38185c
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [hlam, p38185_0]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [h0, hlam, p38185_0]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                rcases p38185_3 (m.d 0 2) (by simp) with h38188 | h38188
                · rcases p38185_3 (m.d 1 2) (by simp) with h38189 | h38189
                  · rcases p38185_3 (m.d 2 3) (by simp) with h38190 | h38190
                    · linarith only [h38190, hlam, p38185_0]
                    · rcases p38185_3 (m.d 2 4) (by simp) with h38192 | h38192
                      · linarith only [h36831, h38192, hlam]
                      · rcases p38185_3 (m.d 2 5) (by simp) with h38194 | h38194
                        · linarith only [h36832, h38194, hlam]
                        · rcases h4bigk with h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c | h38196c
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [hlam, p38196_0]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [h36828, h37309, h37310, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38196_1]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [h36828, h37309, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38196_1]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [h36828, h37309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38196_1]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [h36835, hlam, p38196_0]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [h36828, hlam, p38196_0]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [hlam, p38196_0]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [h36828, h37309, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38196_1]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [h36829, h37309, h37314, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38196_1]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [h37314, hlam, p38196_0]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [h36831, hlam, p38196_0]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [h37310, hlam, p38196_0]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [hlam, p38196_0]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [h36829, h36831, h36835, h37309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38196_1]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [h37318, hlam, p38196_0]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [h36833, hlam, p38196_0]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [h37312, hlam, p38196_0]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [h37316, hlam, p38196_0]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [hlam, p38196_0]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [h37320, hlam, p38196_0]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            rcases p38196_3 (m.d 0 4) (by simp) with h38217 | h38217
                            · linarith only [h38217, hlam, p38196_0]
                            · rcases p38196_3 (m.d 1 4) (by simp) with h38219 | h38219
                              · linarith only [h37314, h38219, hlam]
                              · rcases p38196_3 (m.d 2 4) (by simp) with h38221 | h38221
                                · linarith only [h37318, h38221, hlam]
                                · rcases p38196_3 (m.d 3 4) (by simp) with h38223 | h38223
                                  · linarith only [h37320, h38223, hlam]
                                  · rcases p38196_3 (m.d 4 5) (by simp) with h38225 | h38225
                                    · rcases h5bigk with h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c | h38226c
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [hlam, p38226_0]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h36829, h37309, h37314, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38226_1]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h36829, h37309, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p37322_1, p38226_1]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h36829, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38226_1]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h36835, hlam, p38226_0]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h36829, hlam, p38226_0]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [hlam, p38226_0]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h36829, h37309, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p37322_1, p38226_1]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h36829, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38226_1]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h37314, hlam, p38226_0]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h36832, hlam, p38226_1]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h37311, hlam, p38226_1]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [hlam, p38226_0]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h0, h36832, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38226_1]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h37318, hlam, p38226_0]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h36834, hlam, p38226_1]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h37313, hlam, p38226_1]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h37317, hlam, p38226_0]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [hlam, p38226_0]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h37320, hlam, p38226_0]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h36834, h37320, hc34, hc45, hlam, hphi, p38226_1]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h37313, h37320, hc34, hc45, hlam, hphi, p38226_1]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h37317, h37320, hc34, hc45, hlam, hphi, p38226_1]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [h37320, hc34, hc45, hlam, hphi, p38226_1]
                                      · have p38226_0 := h38226c.1
                                        have p38226_1 := h38226c.2.1
                                        have p38226_2 := h38226c.2.2.1
                                        have p38226_3 := h38226c.2.2.2
                                        linarith only [hlam, p38226_0]
                                    · linarith only [h38225, hlam, p38196_0]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            rcases p38196_3 (m.d 0 4) (by simp) with h38253 | h38253
                            · linarith only [h36835, h38253, hlam]
                            · linarith only [h36828, h38253, hlam]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            rcases p38196_3 (m.d 0 4) (by simp) with h38256 | h38256
                            · linarith only [h36835, h38256, hlam]
                            · linarith only [h36831, h38256, hlam]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            rcases p38196_3 (m.d 0 4) (by simp) with h38259 | h38259
                            · linarith only [h36835, h38259, hlam]
                            · linarith only [h36833, h38259, hlam]
                          · have p38196_0 := h38196c.1
                            have p38196_1 := h38196c.2.1
                            have p38196_2 := h38196c.2.2.1
                            have p38196_3 := h38196c.2.2.2
                            linarith only [hlam, p38196_0]
                  · linarith only [h37309, h38189, hlam]
                · linarith only [h38188, hlam, p38185_0]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                rcases p38185_3 (m.d 0 2) (by simp) with h38265 | h38265
                · rcases p38185_3 (m.d 1 2) (by simp) with h38266 | h38266
                  · rcases p38185_3 (m.d 2 3) (by simp) with h38267 | h38267
                    · linarith only [h36830, h38267, hlam]
                    · linarith only [h37316, h38267, hlam]
                  · linarith only [h37310, h38266, hlam]
                · linarith only [h38265, hlam, p38185_0]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                rcases p38185_3 (m.d 0 2) (by simp) with h38272 | h38272
                · rcases p38185_3 (m.d 1 2) (by simp) with h38273 | h38273
                  · rcases p38185_3 (m.d 2 3) (by simp) with h38274 | h38274
                    · linarith only [h36830, h38274, hlam]
                    · linarith only [h37317, h38274, hlam]
                  · linarith only [h37311, h38273, hlam]
                · linarith only [h38272, hlam, p38185_0]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [h36830, h37317, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38185_1]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [hlam, p38185_0]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                rcases p38185_3 (m.d 0 2) (by simp) with h38281 | h38281
                · linarith only [h0, h38281, hlam]
                · linarith only [h36830, h38281, hlam]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [h36828, h37309, h37310, hlam, p37322_1, p38185_2]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [h36829, h37309, h37311, hlam, p37322_1, p38185_2]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [h36830, hlam, p38185_0]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [h37309, hlam, p38185_0]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [hlam, p38185_0]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                rcases p38185_3 (m.d 0 2) (by simp) with h38289 | h38289
                · rcases p38185_3 (m.d 1 2) (by simp) with h38290 | h38290
                  · rcases p38185_3 (m.d 2 3) (by simp) with h38291 | h38291
                    · rcases p38185_3 (m.d 2 4) (by simp) with h38292 | h38292
                      · linarith only [h37316, h38292, hlam]
                      · rcases p38185_3 (m.d 2 5) (by simp) with h38294 | h38294
                        · linarith only [h37317, h38294, hlam]
                        · linarith only [h37318, h38294, hlam]
                    · linarith only [h37316, h38291, hlam]
                  · linarith only [h37310, h38290, hlam]
                · linarith only [h36831, h38289, hlam]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                rcases p38185_3 (m.d 0 2) (by simp) with h38300 | h38300
                · rcases p38185_3 (m.d 1 2) (by simp) with h38301 | h38301
                  · rcases p38185_3 (m.d 2 3) (by simp) with h38302 | h38302
                    · rcases p38185_3 (m.d 2 4) (by simp) with h38303 | h38303
                      · linarith only [h37316, h38303, hlam]
                      · rcases p38185_3 (m.d 2 5) (by simp) with h38305 | h38305
                        · linarith only [h37317, h38305, hlam]
                        · rcases h4bigk with h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c | h38307c
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [hlam, p38307_0]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [h36828, h37309, h37310, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38307_1]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [h36828, h37309, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38307_1]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [h36828, h37309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38307_1]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [h36835, hlam, p38307_0]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [h36828, hlam, p38307_0]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [hlam, p38307_0]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [h36828, h37309, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38307_1]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [h36829, h37309, h37314, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38307_1]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [h37314, hlam, p38307_0]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [h36831, hlam, p38307_0]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [h37310, hlam, p38307_0]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [hlam, p38307_0]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [h36829, h36831, h36835, h37309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38307_1]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [h37318, hlam, p38307_0]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [h36833, hlam, p38307_0]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [h37312, hlam, p38307_0]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [h37316, hlam, p38307_0]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [hlam, p38307_0]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [h37320, hlam, p38307_0]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            rcases p38307_3 (m.d 0 4) (by simp) with h38328 | h38328
                            · linarith only [h38328, hlam, p38307_0]
                            · rcases p38307_3 (m.d 1 4) (by simp) with h38330 | h38330
                              · linarith only [h37314, h38330, hlam]
                              · rcases p38307_3 (m.d 2 4) (by simp) with h38332 | h38332
                                · linarith only [h37318, h38332, hlam]
                                · rcases p38307_3 (m.d 3 4) (by simp) with h38334 | h38334
                                  · linarith only [h37320, h38334, hlam]
                                  · rcases p38307_3 (m.d 4 5) (by simp) with h38336 | h38336
                                    · rcases h5bigk with h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c | h38337c
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [hlam, p38337_0]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h36829, h37309, h37314, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38337_1]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h36829, h37309, h37317, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38337_1]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h36829, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38337_1]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h36835, hlam, p38337_0]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h36829, hlam, p38337_0]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [hlam, p38337_0]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h36829, h37309, h37317, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38337_1]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h36829, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38337_1]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h37314, hlam, p38337_0]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h36832, hlam, p38337_1]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h37311, hlam, p38337_1]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [hlam, p38337_0]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h36830, h37320, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p38185_1, p38337_1]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h37318, hlam, p38337_0]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h36834, hlam, p38337_1]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h37313, hlam, p38337_1]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h37317, hlam, p38337_0]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [hlam, p38337_0]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h37320, hlam, p38337_0]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h36834, h37320, hc34, hc45, hlam, hphi, p38337_1]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h37313, h37320, hc34, hc45, hlam, hphi, p38337_1]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h37317, h37320, hc34, hc45, hlam, hphi, p38337_1]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [h37320, hc34, hc45, hlam, hphi, p38337_1]
                                      · have p38337_0 := h38337c.1
                                        have p38337_1 := h38337c.2.1
                                        have p38337_2 := h38337c.2.2.1
                                        have p38337_3 := h38337c.2.2.2
                                        linarith only [hlam, p38337_0]
                                    · linarith only [h38336, hlam, p38307_0]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            rcases p38307_3 (m.d 0 4) (by simp) with h38364 | h38364
                            · linarith only [h36835, h38364, hlam]
                            · linarith only [h36828, h38364, hlam]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            rcases p38307_3 (m.d 0 4) (by simp) with h38367 | h38367
                            · linarith only [h36835, h38367, hlam]
                            · linarith only [h36831, h38367, hlam]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            rcases p38307_3 (m.d 0 4) (by simp) with h38370 | h38370
                            · linarith only [h36835, h38370, hlam]
                            · linarith only [h36833, h38370, hlam]
                          · have p38307_0 := h38307c.1
                            have p38307_1 := h38307c.2.1
                            have p38307_2 := h38307c.2.2.1
                            have p38307_3 := h38307c.2.2.2
                            linarith only [hlam, p38307_0]
                    · linarith only [h37317, h38302, hlam]
                  · linarith only [h37311, h38301, hlam]
                · linarith only [h36832, h38300, hlam]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [h36831, hlam, p38185_0]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [h37310, hlam, p38185_0]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [h37316, hlam, p38185_0]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [hlam, p38185_0]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [h37318, hlam, p38185_0]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [h36832, hlam, p38185_0]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [h37311, hlam, p38185_0]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [h37317, hlam, p38185_0]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [h36829, h36832, h37309, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p38185_1]
              · have p38185_0 := h38185c.1
                have p38185_1 := h38185c.2.1
                have p38185_2 := h38185c.2.2.1
                have p38185_3 := h38185c.2.2.2
                linarith only [hlam, p38185_0]
      · linarith only [h37773, hlam, p37322_0]
    · linarith only [h0, h37772, hlam]

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x11 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h37309 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h37310 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h37311 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h37312 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h37313 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h37314 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h37316 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h37317 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h37318 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h37320 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h37322c : ((m.d 1 3) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 3) ∧ (m.d 1 2) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 2) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have p37322_0 := h37322c.1
  have p37322_1 := h37322c.2.1
  have p37322_2 := h37322c.2.2.1
  have p37322_3 := h37322c.2.2.2
  linarith only [h37309, hlam, p37322_0]

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x12 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h37309 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h37310 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h37311 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h37312 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h37313 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h37314 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h37316 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h37317 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h37318 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h37320 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h37322c : ((m.d 1 3) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 3) ∧ (m.d 1 3) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 3) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have p37322_0 := h37322c.1
  have p37322_1 := h37322c.2.1
  have p37322_2 := h37322c.2.2.1
  have p37322_3 := h37322c.2.2.2
  linarith only [hlam, p37322_0]

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x13 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h37309 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h37310 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h37311 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h37312 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h37313 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h37314 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h37316 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h37317 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h37318 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h37320 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h37322c : ((m.d 1 3) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 3) ∧ (m.d 1 4) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 4) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have p37322_0 := h37322c.1
  have p37322_1 := h37322c.2.1
  have p37322_2 := h37322c.2.2.1
  have p37322_3 := h37322c.2.2.2
  rcases p37322_3 (m.d 0 1) (by simp) with h38391 | h38391
  · linarith only [h33187, h38391, hlam]
  · linarith only [h36828, h38391, hlam]

end R2N4
