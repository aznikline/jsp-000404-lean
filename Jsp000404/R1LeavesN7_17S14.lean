import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_17S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6230000 in
set_option maxHeartbeats 6230000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6421 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7464 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8188 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8818 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8819 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0 := hg0
  have h6421 := hg6421
  have h7464 := hg7464
  rcases m.htr 0 2 5 (by decide) (by decide) with h9764 | h9764
  · rcases m.htr 0 3 4 (by decide) (by decide) with h9765 | h9765
    · linarith only [h8818, h8819, h9765, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h9767 | h9767
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9768 | h9768
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9769 | h9769
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9770 | h9770
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9771 | h9771
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9772 | h9772
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9773 | h9773
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9774 | h9774
                    · linarith only [h8188, h8818, h8819, h9765, h9767, h9770, h9774, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9776 | h9776
                      · linarith only [h8818, h8819, h9769, h9772, h9774, h9776, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h8818, h8819, h9767, h9769, h9772, h9774, h9776, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h7464, h9768, h9773, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9780 | h9780
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9781 | h9781
                    · linarith only [h8818, h8819, h9770, h9772, h9781, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9783 | h9783
                      · linarith only [h8818, h8819, h9770, h9783, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h8818, h8819, h9767, h9770, h9783, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h7464, h8819, h9764, h9768, h9780, hlam]
              · linarith only [h8819, h9764, h9771, hc12, hc24, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9788 | h9788
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9789 | h9789
                · linarith only [h6421, h9765, h9769, h9770, h9789, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9791 | h9791
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9792 | h9792
                    · linarith only [h0, h8818, h9770, h9789, h9792, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9794 | h9794
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9795 | h9795
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9796 | h9796
                          · rcases h0bigk with h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c | h9797c
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [hlam, p9797_0]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h0, hlam, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h6421, hlam, p9797_0]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h7464, hlam, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h8188, hlam, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h0, h9770, h9792, hc01, hc34, hlam, hphi, ht12, ht23, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [hlam, p9797_0]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h0, h8818, h9770, h9792, h9794, h9796, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h8819, hlam, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h0, h8188, h9770, h9792, hc01, hc34, hlam, hphi, ht12, ht23, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h6421, hc01, hc13, hlam, hphi, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h8818, hlam, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [hlam, p9797_0]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h9765, hlam, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h0, h8188, h8818, h9770, h9792, hc01, hc34, hlam, hphi, ht12, ht23, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h7464, h9770, h9792, hc01, hc34, hlam, hphi, ht12, ht23, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h7464, h9770, h9792, hc02, hc34, hlam, hphi, ht23, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h7464, h8818, h9770, h9792, h9794, h9796, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [hlam, p9797_0]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h7464, h8188, h9770, h9792, hc01, hc34, hlam, hphi, ht12, ht23, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h8188, h9770, h9788, h9792, hc01, hc34, hlam, hphi, ht12, ht23, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h9764, hlam, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h9767, hlam, p9797_0]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [h9768, hlam, p9797_1]
                            · have p9797_0 := h9797c.1
                              have p9797_1 := h9797c.2.1
                              have p9797_2 := h9797c.2.2.1
                              have p9797_3 := h9797c.2.2.2
                              linarith only [hlam, p9797_0]
                          · linarith only [h0, h9770, h9792, h9796, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h8818, h9767, h9768, h9770, h9794, h9795, hc03, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h6421, h9767, h9769, h9770, h9792, h9794, hc23, hc34, hlam, hphi]
                  · linarith only [h6421, h7464, h9767, h9768, h9769, h9770, h9791, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h7464, h8819, h9764, h9788, hc01, hc14, hlam, hphi]
          · linarith only [h0, h8818, h9769, hlam]
        · linarith only [h8818, h8819, h9767, h9768, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9830 | h9830
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9831 | h9831
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9832 | h9832
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9833 | h9833
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9834 | h9834
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9835 | h9835
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9836 | h9836
                    · linarith only [h0, h6421, h8818, h9765, h9836, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9838 | h9838
                      · linarith only [h6421, h8818, h8819, h9767, h9831, h9834, h9836, h9838, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9840 | h9840
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9841 | h9841
                          · rcases h0bigk with h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c | h9842c
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [hlam, p9842_0]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h0, hlam, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h6421, hlam, p9842_0]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h7464, hlam, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h8188, hlam, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h8819, h9831, h9834, h9836, hc01, hc12, hlam, hphi, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [hlam, p9842_0]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h6421, h8819, h9831, h9834, h9836, hc01, hc12, hlam, hphi, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h8819, hlam, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h8819, h9831, h9834, h9836, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h8819, h9764, h9767, h9831, h9834, h9836, h9838, hc01, hc12, hc23, hc35, hlam, hphi, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h8818, hlam, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [hlam, p9842_0]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h9765, hlam, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h9767, hlam, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h8819, h9831, h9834, h9836, hc01, hc12, hlam, hphi, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h8819, h9764, h9831, h9834, h9836, h9838, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h8819, h9831, h9834, h9836, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [hlam, p9842_0]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h6421, h8819, h9767, h9831, h9834, h9836, hc01, hc12, hlam, hphi, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h8188, h9831, h9834, h9835, hc01, hc12, hlam, hphi, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h9764, hlam, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h0, h6421, h9764, hc01, hc12, hlam, hphi, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [h9830, hlam, p9842_1]
                            · have p9842_0 := h9842c.1
                              have p9842_1 := h9842c.2.1
                              have p9842_2 := h9842c.2.2.1
                              have p9842_3 := h9842c.2.2.2
                              linarith only [hlam, p9842_0]
                          · linarith only [h8818, h8819, h9836, h9841, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h8819, h9764, h9830, h9840, hlam]
                  · linarith only [h7464, h8819, h9764, h9830, h9835, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9871 | h9871
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9872 | h9872
                    · linarith only [h6421, h9834, h9872, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9874 | h9874
                      · linarith only [h8818, h8819, h9832, h9874, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9876 | h9876
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9877 | h9877
                          · rcases h0bigk with h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c | h9878c
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [hlam, p9878_0]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h0, hlam, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h6421, hlam, p9878_0]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h7464, hlam, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h8188, hlam, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h8819, h9832, hc01, hc12, hlam, hphi, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [hlam, p9878_0]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h6421, h8819, h9832, hc01, hc12, hlam, hphi, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h8819, hlam, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h8819, h9832, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h9767, hc01, hc35, hlam, hphi, ht12, ht23, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h8818, hlam, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [hlam, p9878_0]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h9765, hlam, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h9767, hlam, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h8819, h9832, hc01, hc12, hlam, hphi, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h8819, h9832, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h8819, h9832, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [hlam, p9878_0]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h6421, h8819, h9767, h9832, hc01, hc12, hlam, hphi, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h8188, h9871, hc01, hc14, hlam, hphi, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h9764, hlam, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h6421, h8819, h9764, h9832, hc01, hc12, hlam, hphi, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [h9830, hlam, p9878_1]
                            · have p9878_0 := h9878c.1
                              have p9878_1 := h9878c.2.1
                              have p9878_2 := h9878c.2.2.1
                              have p9878_3 := h9878c.2.2.2
                              linarith only [hlam, p9878_0]
                          · linarith only [h7464, h9830, h9834, h9877, hlam]
                        · linarith only [h8819, h9764, h9830, h9876, hc04, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h8819, h9764, h9830, h9832, h9871, hlam]
              · linarith only [h8819, h9764, h9832, h9833, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9908 | h9908
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9909 | h9909
                · linarith only [h6421, h9765, h9831, h9832, h9909, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9911 | h9911
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9912 | h9912
                    · linarith only [h0, h6421, h8818, h9832, h9909, h9912, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9914 | h9914
                      · linarith only [h0, h8818, h9767, h9832, h9912, h9914, hc03, hc34, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9916 | h9916
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9917 | h9917
                          · rcases h0bigk with h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [hlam, p9918_0]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h0, hlam, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h6421, hlam, p9918_0]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h7464, hlam, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h8188, hlam, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h0, h9832, h9912, hc01, hc34, hlam, hphi, ht12, ht23, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [hlam, p9918_0]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h0, h6421, h9832, h9912, hc01, hc34, hlam, hphi, ht12, ht23, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h8819, hlam, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h0, h9832, h9912, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h6421, hc01, hc13, hlam, hphi, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h8818, hlam, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [hlam, p9918_0]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h9765, hlam, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h9767, hlam, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h7464, h9832, h9912, hc01, hc34, hlam, hphi, ht12, ht23, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h7464, h9832, h9912, hc02, hc34, hlam, hphi, ht23, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h7464, h9832, h9912, hc03, hc34, hlam, hphi, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [hlam, p9918_0]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h6421, h7464, h9767, h9832, h9912, hc01, hc34, hlam, hphi, ht12, ht23, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h8188, h9832, h9908, h9912, hc01, hc34, hlam, hphi, ht12, ht23, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h9764, hlam, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h0, h6421, h9764, h9832, h9912, hc01, hc34, hlam, hphi, ht12, ht23, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [h9830, hlam, p9918_1]
                            · have p9918_0 := h9918c.1
                              have p9918_1 := h9918c.2.1
                              have p9918_2 := h9918c.2.2.1
                              have p9918_3 := h9918c.2.2.2
                              linarith only [hlam, p9918_0]
                          · linarith only [h0, h9764, h9832, h9912, h9916, h9917, hlam]
                        · linarith only [h0, h9832, h9916, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h7464, h9764, h9830, h9832, h9911, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h9764, h9908, hlam]
          · linarith only [h0, h8818, h9831, hlam]
        · linarith only [h8819, h9764, h9830, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h9950 | h9950
    · linarith only [h8818, h8819, h9950, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h9952 | h9952
      · linarith only [h8818, h9764, h9952, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9954 | h9954
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9955 | h9955
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9956 | h9956
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9957 | h9957
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9958 | h9958
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9959 | h9959
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9960 | h9960
                    · linarith only [h8818, h8819, h9950, h9956, h9960, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9962 | h9962
                      · linarith only [h6421, h8818, h8819, h9952, h9955, h9958, h9960, h9962, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9964 | h9964
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9965 | h9965
                          · rcases h0bigk with h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c | h9966c
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [hlam, p9966_0]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h0, hlam, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h6421, hlam, p9966_0]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h7464, hlam, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h8188, hlam, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h9764, h9955, h9958, h9960, h9964, hc01, hc12, hlam, hphi, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [hlam, p9966_0]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h6421, h9764, h9955, h9958, h9960, h9964, hc01, hc12, hlam, hphi, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h8819, hlam, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h9764, hlam, p9966_0]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h6421, h9955, hc01, hc12, hlam, hphi, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h8818, hlam, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [hlam, p9966_0]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h9950, hlam, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h9952, hlam, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h7464, hc01, hc14, hlam, hphi, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h8818, h8819, h9955, h9958, h9960, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h8819, h9955, h9958, h9960, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [hlam, p9966_0]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h8818, h8819, h9764, h9955, h9958, h9960, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h8188, hc01, hc15, hlam, hphi, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h8818, h9764, h9955, h9958, h9960, h9964, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h6421, h9764, h9955, h9958, h9960, h9964, hc01, hc12, hlam, hphi, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [h9954, hlam, p9966_1]
                            · have p9966_0 := h9966c.1
                              have p9966_1 := h9966c.2.1
                              have p9966_2 := h9966c.2.2.1
                              have p9966_3 := h9966c.2.2.2
                              linarith only [hlam, p9966_0]
                          · linarith only [h8819, h9954, h9960, h9965, hlam]
                        · linarith only [h8819, h9954, h9964, hlam]
                  · linarith only [h7464, h8819, h9954, h9959, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9995 | h9995
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9996 | h9996
                    · linarith only [h6421, h8818, h9958, h9996, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9998 | h9998
                      · linarith only [h8188, h8818, h9764, h9952, h9957, h9995, h9998, hc01, hc14, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10000 | h10000
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10001 | h10001
                          · rcases h0bigk with h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c | h10002c
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [hlam, p10002_0]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h0, hlam, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h6421, hlam, p10002_0]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h7464, hlam, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h8188, hlam, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h10000, h9764, h9956, hc01, hc12, hlam, hphi, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [hlam, p10002_0]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h10000, h6421, h9764, h9956, hc01, hc12, hlam, hphi, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h8819, hlam, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h9764, hlam, p10002_0]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h6421, hc01, hc13, hlam, hphi, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h8818, hlam, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [hlam, p10002_0]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h9950, hlam, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h9952, hlam, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h8819, h9956, hc01, hc12, hlam, hphi, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h8819, h9956, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h8819, h9956, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [hlam, p10002_0]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h8818, h8819, h9764, h9956, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h8188, h9958, h9995, hc01, hc34, hlam, hphi, ht12, ht23, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h10000, h8818, h9764, h9956, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h10000, h6421, h9764, h9956, hc01, hc12, hlam, hphi, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [h9954, hlam, p10002_1]
                            · have p10002_0 := h10002c.1
                              have p10002_1 := h10002c.2.1
                              have p10002_2 := h10002c.2.2.1
                              have p10002_3 := h10002c.2.2.2
                              linarith only [hlam, p10002_0]
                          · linarith only [h10001, h8819, h9954, h9956, h9958, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h10000, h8819, h9954, hlam]
                  · linarith only [h8819, h9954, h9956, h9995, hlam]
              · linarith only [h8818, h8819, h9956, h9957, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10032 | h10032
              · linarith only [h10032, h8818, h9764, h9956, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10034 | h10034
                · linarith only [h10034, h6421, h9950, h9955, h9956, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10036 | h10036
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10037 | h10037
                    · linarith only [h0, h10034, h10037, h8818, h9956, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10039 | h10039
                      · linarith only [h10039, h8818, h9952, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10041 | h10041
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10042 | h10042
                          · rcases h0bigk with h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c | h10043c
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [hlam, p10043_0]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h0, hlam, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h6421, hlam, p10043_0]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h7464, hlam, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h8188, hlam, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h0, h10032, h10037, h10041, hc01, hc34, hlam, hphi, ht12, ht23, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [hlam, p10043_0]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h0, h10032, h10037, h10041, hc03, hc34, hlam, hphi, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h8819, hlam, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h9764, hlam, p10043_0]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h6421, hc01, hc13, hlam, hphi, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h8818, hlam, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [hlam, p10043_0]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h9950, hlam, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h9952, hlam, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h7464, hc01, hc14, hlam, hphi, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h10037, h8819, hc02, hc34, hlam, hphi, ht23, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h10037, h6421, h8819, hc01, hc34, hlam, hphi, ht12, ht23, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [hlam, p10043_0]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h10037, h8818, h8819, h9764, hc23, hc34, hlam, hphi, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h8188, hc01, hc15, hlam, hphi, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h10037, h10041, h8818, h9764, hc23, hc34, hlam, hphi, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h10037, h10041, h6421, h9764, hc01, hc34, hlam, hphi, ht12, ht23, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [h9954, hlam, p10043_1]
                            · have p10043_0 := h10043c.1
                              have p10043_1 := h10043c.2.1
                              have p10043_2 := h10043c.2.2.1
                              have p10043_3 := h10043c.2.2.2
                              linarith only [hlam, p10043_0]
                          · linarith only [h10037, h10042, h7464, h9954, h9956, hlam]
                        · linarith only [h10041, h7464, h9954, h9956, hlam]
                  · linarith only [h10036, h7464, h9954, hlam]
          · linarith only [h0, h8818, h9955, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10073 | h10073
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10074 | h10074
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10075 | h10075
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10076 | h10076
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10077 | h10077
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10078 | h10078
                    · linarith only [h10073, h10076, h10077, h10078, h6421, h8818, h8819, h9950, h9954, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10080 | h10080
                      · linarith only [h10073, h10076, h10077, h10080, h8818, h8819, h9954, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10082 | h10082
                        · linarith only [h10078, h10082, h8818, h8819, h9954, hc23, hc34, hlam, hphi]
                        · linarith only [h10073, h10076, h10077, h10082, h8818, h8819, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h10074, h10077, h8818, h8819, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10086 | h10086
                  · linarith only [h10076, h10086, h8818, h8819, h9954, hc23, hc34, hlam, hphi]
                  · linarith only [h10074, h10086, h8818, h8819, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h10074, h10075, h8818, h8819, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10090 | h10090
              · linarith only [h10074, h10090, h8818, h9764, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10092 | h10092
                · linarith only [h10073, h10074, h10092, h6421, h9950, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10094 | h10094
                  · linarith only [h10092, h10094, h8818, h8819, h9954, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10096 | h10096
                    · linarith only [h0, h10074, h10094, h10096, h8818, hc34, hc45, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10098 | h10098
                      · linarith only [h10098, h8818, h9952, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10100 | h10100
                        · linarith only [h0, h10074, h10094, h10096, h10100, h8818, hc23, hc34, hlam, hphi]
                        · linarith only [h10100, h8818, h8819, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h10073, h8818, h8819, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 6230000 in
set_option maxHeartbeats 6230000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6421 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7464 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8188 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8818 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0 := hg0
  have h6421 := hg6421
  have h7464 := hg7464
  rcases m.htr 0 2 4 (by decide) (by decide) with h8819 | h8819
  · exact r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x0_x0 m hb0 hb2 hb4 hg0 hg6421 hg7464 h8188 h8818 h8819
  · exact r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x0_x1 m hb0 hb2 hb4 hg0 hg6421 hg7464 h8188 h8818 h8819

end R2N4
