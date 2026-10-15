import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_15S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6253 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7338 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8081 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8735 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8736 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h6253 := hg6253
  have h7338 := hg7338
  have h8081 := hg8081
  rcases m.htr 0 2 5 (by decide) (by decide) with h9748 | h9748
  · rcases m.htr 0 3 4 (by decide) (by decide) with h9749 | h9749
    · linarith only [h8735, h8736, h9749, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h9751 | h9751
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9752 | h9752
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9753 | h9753
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9754 | h9754
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9755 | h9755
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9756 | h9756
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9757 | h9757
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9758 | h9758
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9759 | h9759
                      · linarith only [h8081, h8735, h8736, h9749, h9751, h9754, h9759, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9761 | h9761
                        · linarith only [h8735, h8736, h9753, h9756, h9759, h9761, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h8735, h8736, h9751, h9753, h9756, h9759, h9761, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h7338, h9752, h9758, hlam]
                  · linarith only [h6253, h9751, h9757, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9766 | h9766
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9767 | h9767
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9768 | h9768
                      · linarith only [h8735, h8736, h9754, h9756, h9768, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9770 | h9770
                        · linarith only [h8735, h8736, h9754, h9770, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h8735, h8736, h9751, h9754, h9770, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h8735, h8736, h9751, h9752, h9754, h9767, hc04, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h6253, h9751, h9766, hlam]
              · linarith only [h8735, h8736, h9754, h9755, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9776 | h9776
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9777 | h9777
                · linarith only [h9749, h9751, h9753, h9754, h9777, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9779 | h9779
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9780 | h9780
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9781 | h9781
                      · linarith only [h8081, h9777, h9779, h9781, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9783 | h9783
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h9784 | h9784
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h9785 | h9785
                            · rcases h0bigk with h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c | h9786c
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [hlam, p9786_0]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h0, hlam, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h6253, hlam, p9786_0]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h7338, hlam, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h8081, hlam, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [hlam, p9786_0]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h0, h9754, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h8736, hlam, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h0, h8081, h9754, h9781, hc01, hc34, hlam, hphi, ht12, ht23, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h6253, h9753, h9754, h9781, hc01, hc34, hlam, hphi, ht12, ht23, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h8735, hlam, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [hlam, p9786_0]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h9749, hlam, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h6253, h8081, h9753, h9754, h9781, hc01, hc34, hlam, hphi, ht12, ht23, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h8736, h9781, hc01, hc34, hlam, hphi, ht12, ht23, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h8736, h9781, hc02, hc34, hlam, hphi, ht23, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h8736, h9781, hc03, hc34, hlam, hphi, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [hlam, p9786_0]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h8081, h8736, h9781, hc01, hc34, hlam, hphi, ht12, ht23, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h8081, h9753, h9754, h9779, h9781, hc01, hc34, hlam, hphi, ht12, ht23, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h9748, hlam, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h9751, hlam, p9786_0]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [h9752, hlam, p9786_1]
                              · have p9786_0 := h9786c.1
                                have p9786_1 := h9786c.2.1
                                have p9786_2 := h9786c.2.2.1
                                have p9786_3 := h9786c.2.2.2
                                linarith only [hlam, p9786_0]
                            · linarith only [h0, h9754, h9781, h9785, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h8081, h9752, h9753, h9754, h9779, h9784, hlam]
                        · linarith only [h6253, h9751, h9753, h9754, h9781, h9783, hc23, hc34, hlam, hphi]
                    · linarith only [h7338, h8081, h9752, h9777, h9779, h9780, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h6253, h9751, h9779, hlam]
              · linarith only [h0, h9748, h9776, hlam]
          · linarith only [h0, h8735, h9753, hlam]
        · linarith only [h8736, h9748, h9752, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9820 | h9820
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9821 | h9821
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9822 | h9822
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9823 | h9823
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9824 | h9824
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9825 | h9825
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9826 | h9826
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9827 | h9827
                      · linarith only [h8735, h8736, h9749, h9822, h9827, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9829 | h9829
                        · linarith only [h6253, h8735, h8736, h9751, h9821, h9824, h9827, h9829, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h9831 | h9831
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h9832 | h9832
                            · rcases h0bigk with h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c | h9833c
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [hlam, p9833_0]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h0, hlam, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h6253, hlam, p9833_0]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h7338, hlam, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h8081, hlam, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h8736, h9821, h9824, h9827, hc01, hc12, hlam, hphi, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [hlam, p9833_0]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h6253, h8736, h9821, h9824, h9827, hc01, hc12, hlam, hphi, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h8736, hlam, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h8736, h9821, h9824, h9827, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h9751, h9825, hc01, hc15, hlam, hphi, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h8735, hlam, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [hlam, p9833_0]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h9749, hlam, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h9751, hlam, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h7338, hc01, hc14, hlam, hphi, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h8736, h9748, h9821, h9824, h9827, h9829, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h8736, h9821, h9824, h9827, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [hlam, p9833_0]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h6253, h8736, h9751, h9821, h9824, h9827, hc01, hc12, hlam, hphi, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h8081, hc01, hc15, hlam, hphi, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h9748, hlam, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h0, h6253, h9748, hc01, hc12, hlam, hphi, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [h9820, hlam, p9833_1]
                              · have p9833_0 := h9833c.1
                                have p9833_1 := h9833c.2.1
                                have p9833_2 := h9833c.2.2.1
                                have p9833_3 := h9833c.2.2.2
                                linarith only [hlam, p9833_0]
                            · linarith only [h8735, h8736, h9827, h9832, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h8736, h9748, h9820, h9831, hlam]
                    · linarith only [h7338, h8736, h9748, h9820, h9826, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h8735, h8736, h9749, h9824, h9825, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9863 | h9863
                  · linarith only [h6253, h9751, h9824, h9863, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9865 | h9865
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9866 | h9866
                      · linarith only [h8735, h8736, h9822, h9824, h9866, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9868 | h9868
                        · linarith only [h6253, h8735, h8736, h9822, h9863, h9868, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h9870 | h9870
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h9871 | h9871
                            · rcases h0bigk with h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h0, hlam, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h6253, hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h7338, hlam, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h8081, hlam, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h8736, h9822, hc01, hc12, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h6253, h8736, h9822, hc01, hc12, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h8736, hlam, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h8736, h9822, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h6253, hc01, hc13, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h8735, hlam, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9749, hlam, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9751, hlam, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h8736, h9822, hc01, hc12, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h8736, h9822, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h8736, h9822, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h6253, h8736, h9751, h9822, hc01, hc12, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h8081, h9865, hc01, hc14, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9748, hlam, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h6253, h8736, h9748, h9822, hc01, hc12, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9820, hlam, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hlam, p9872_0]
                            · linarith only [h7338, h9820, h9824, h9871, hlam]
                          · linarith only [h8736, h9748, h9820, h9870, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h8736, h9748, h9820, h9822, h9865, hlam]
              · linarith only [h8736, h9748, h9822, h9823, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9902 | h9902
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9903 | h9903
                · linarith only [h6253, h9749, h9821, h9822, h9903, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9905 | h9905
                  · linarith only [h6253, h9751, h9903, h9905, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9907 | h9907
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9908 | h9908
                      · linarith only [h8735, h9749, h9908, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9910 | h9910
                        · linarith only [h0, h8735, h9822, h9905, h9908, h9910, hc13, hc34, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h9912 | h9912
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h9913 | h9913
                            · rcases h0bigk with h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c | h9914c
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [hlam, p9914_0]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h0, hlam, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h6253, hlam, p9914_0]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h7338, hlam, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h8081, hlam, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h0, h9822, h9908, hc01, hc34, hlam, hphi, ht12, ht23, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [hlam, p9914_0]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h0, h6253, h9822, h9908, hc01, hc34, hlam, hphi, ht12, ht23, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h8736, hlam, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h0, h9822, h9908, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h6253, hc01, hc13, hlam, hphi, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h8735, hlam, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [hlam, p9914_0]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h9749, hlam, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h9751, hlam, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h7338, hc01, hc14, hlam, hphi, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h8736, h9908, hc02, hc34, hlam, hphi, ht23, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h6253, h8736, h9908, hc01, hc34, hlam, hphi, ht12, ht23, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [hlam, p9914_0]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h6253, h8736, h9751, h9908, hc01, hc34, hlam, hphi, ht12, ht23, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h8081, h9822, h9902, h9908, hc01, hc34, hlam, hphi, ht12, ht23, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h9748, hlam, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h6253, h8081, h9822, h9902, h9908, hc01, hc34, hlam, hphi, ht12, ht23, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [h9820, hlam, p9914_1]
                              · have p9914_0 := h9914c.1
                                have p9914_1 := h9914c.2.1
                                have p9914_2 := h9914c.2.2.1
                                have p9914_3 := h9914c.2.2.2
                                linarith only [hlam, p9914_0]
                            · linarith only [h0, h9822, h9908, h9913, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h6253, h9822, h9902, h9905, h9912, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h7338, h9748, h9820, h9822, h9907, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h9748, h9902, hlam]
          · linarith only [h0, h8735, h9821, hlam]
        · linarith only [h8736, h9748, h9820, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h9946 | h9946
    · linarith only [h8735, h8736, h9946, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h9948 | h9948
      · linarith only [h8735, h9748, h9948, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9950 | h9950
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9951 | h9951
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9952 | h9952
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9953 | h9953
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9954 | h9954
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9955 | h9955
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9956 | h9956
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9957 | h9957
                      · linarith only [h8735, h8736, h9946, h9952, h9957, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9959 | h9959
                        · linarith only [h6253, h8735, h8736, h9948, h9951, h9954, h9957, h9959, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h9961 | h9961
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h9962 | h9962
                            · rcases h0bigk with h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c | h9963c
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [hlam, p9963_0]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h0, hlam, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h6253, hlam, p9963_0]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h7338, hlam, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h8081, hlam, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h9748, h9951, h9954, h9957, h9961, hc01, hc12, hlam, hphi, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [hlam, p9963_0]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h6253, h9748, h9951, h9954, h9957, h9961, hc01, hc12, hlam, hphi, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h8736, hlam, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h9748, hlam, p9963_0]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h6253, h9951, hc01, hc12, hlam, hphi, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h8735, hlam, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [hlam, p9963_0]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h9946, hlam, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h9948, hlam, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h7338, hc01, hc14, hlam, hphi, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h8735, h8736, h9951, h9954, h9957, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h8736, h9951, h9954, h9957, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [hlam, p9963_0]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h8735, h8736, h9748, h9951, h9954, h9957, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h8081, hc01, hc15, hlam, hphi, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h8735, h9748, h9951, h9954, h9957, h9961, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h6253, h9748, h9951, h9954, h9957, h9961, hc01, hc12, hlam, hphi, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [h9950, hlam, p9963_1]
                              · have p9963_0 := h9963c.1
                                have p9963_1 := h9963c.2.1
                                have p9963_2 := h9963c.2.2.1
                                have p9963_3 := h9963c.2.2.2
                                linarith only [hlam, p9963_0]
                            · linarith only [h8736, h9950, h9957, h9962, hlam]
                          · linarith only [h8736, h9950, h9961, hlam]
                    · linarith only [h7338, h8736, h9950, h9956, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h8735, h8736, h9946, h9954, h9955, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9993 | h9993
                  · linarith only [h6253, h9948, h9954, h9993, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9995 | h9995
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9996 | h9996
                      · linarith only [h8735, h8736, h9954, h9996, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9998 | h9998
                        · linarith only [h8735, h9748, h9953, h9993, h9998, hlam]
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
                                linarith only [h6253, hlam, p10002_0]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h7338, hlam, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h8081, hlam, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h10000, h9748, h9952, hc01, hc12, hlam, hphi, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [hlam, p10002_0]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h10000, h6253, h9748, h9952, hc01, hc12, hlam, hphi, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h8736, hlam, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h9748, hlam, p10002_0]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h6253, hc01, hc13, hlam, hphi, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h8735, hlam, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [hlam, p10002_0]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h9946, hlam, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h9948, hlam, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h7338, hc01, hc14, hlam, hphi, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h8736, h9952, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h8736, h9952, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [hlam, p10002_0]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h8735, h8736, h9748, h9952, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h8081, hc01, hc15, hlam, hphi, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h10000, h8735, h9748, h9952, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h10000, h6253, h9748, h9952, hc01, hc12, hlam, hphi, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [h9950, hlam, p10002_1]
                              · have p10002_0 := h10002c.1
                                have p10002_1 := h10002c.2.1
                                have p10002_2 := h10002c.2.2.1
                                have p10002_3 := h10002c.2.2.2
                                linarith only [hlam, p10002_0]
                            · linarith only [h10001, h8736, h9950, h9952, h9954, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h10000, h8736, h9950, hlam]
                    · linarith only [h8736, h9950, h9952, h9995, hlam]
              · linarith only [h8735, h8736, h9952, h9953, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10032 | h10032
              · linarith only [h10032, h8735, h9748, h9952, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10034 | h10034
                · linarith only [h10034, h6253, h9946, h9951, h9952, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10036 | h10036
                  · linarith only [h10034, h10036, h6253, h9948, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10038 | h10038
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10039 | h10039
                      · linarith only [h0, h10034, h10039, h8735, h9952, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10041 | h10041
                        · linarith only [h10036, h10041, h6253, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10043 | h10043
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10044 | h10044
                            · rcases h0bigk with h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c | h10045c
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [hlam, p10045_0]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h0, hlam, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h6253, hlam, p10045_0]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h7338, hlam, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h8081, hlam, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h0, h10032, h10039, h10043, hc01, hc34, hlam, hphi, ht12, ht23, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [hlam, p10045_0]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h0, h10032, h10039, h10043, hc03, hc34, hlam, hphi, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h8736, hlam, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h9748, hlam, p10045_0]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h10032, h10039, h10043, h6253, h9951, hc01, hc34, hlam, hphi, ht12, ht23, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h8735, hlam, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [hlam, p10045_0]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h9946, hlam, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h9948, hlam, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h7338, hc01, hc14, hlam, hphi, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h10039, h8736, hc02, hc34, hlam, hphi, ht23, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h10039, h8736, hc03, hc34, hlam, hphi, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [hlam, p10045_0]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h10039, h8735, h8736, h9748, hc23, hc34, hlam, hphi, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h8081, hc01, hc15, hlam, hphi, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h10039, h10043, h8735, h9748, hc23, hc34, hlam, hphi, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h10039, h10043, h6253, h9748, hc01, hc34, hlam, hphi, ht12, ht23, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [h9950, hlam, p10045_1]
                              · have p10045_0 := h10045c.1
                                have p10045_1 := h10045c.2.1
                                have p10045_2 := h10045c.2.2.1
                                have p10045_3 := h10045c.2.2.2
                                linarith only [hlam, p10045_0]
                            · linarith only [h10039, h10044, h7338, h9950, h9952, hlam]
                          · linarith only [h10043, h7338, h9950, h9952, hlam]
                    · linarith only [h10038, h7338, h9950, hlam]
          · linarith only [h0, h8735, h9951, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10075 | h10075
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10076 | h10076
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10077 | h10077
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10078 | h10078
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10079 | h10079
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10080 | h10080
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10081 | h10081
                      · linarith only [h10078, h10080, h10081, h6253, h8735, h8736, h9946, h9950, hc01, hc13, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10083 | h10083
                        · linarith only [h10075, h10078, h10080, h10083, h8735, h8736, h9950, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10085 | h10085
                          · linarith only [h10081, h10085, h8735, h8736, h9950, hc23, hc34, hlam, hphi]
                          · linarith only [h10075, h10078, h10080, h10085, h8735, h8736, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h10076, h10080, h8735, h8736, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h10078, h10079, h6253, h9946, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10090 | h10090
                  · linarith only [h10078, h10090, h6253, h9948, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10092 | h10092
                    · linarith only [h10078, h10092, h8735, h8736, h9950, hc23, hc34, hlam, hphi]
                    · linarith only [h10076, h10092, h8735, h8736, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h10076, h10077, h8735, h8736, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10096 | h10096
              · linarith only [h10076, h10096, h8735, h9748, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10098 | h10098
                · linarith only [h10075, h10076, h10098, h6253, h9946, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10100 | h10100
                  · linarith only [h10098, h10100, h6253, h9948, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10102 | h10102
                    · linarith only [h10098, h10102, h8735, h8736, h9950, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10104 | h10104
                      · linarith only [h10104, h8735, h9946, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10106 | h10106
                        · linarith only [h10106, h8735, h9948, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10108 | h10108
                          · linarith only [h0, h10076, h10102, h10104, h10108, h8735, hc23, hc34, hlam, hphi]
                          · linarith only [h10108, h8735, h8736, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h10075, h8735, h8736, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6253 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7338 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8081 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8735 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h6253 := hg6253
  have h7338 := hg7338
  have h8081 := hg8081
  rcases m.htr 0 2 4 (by decide) (by decide) with h8736 | h8736
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6253 hg7338 hg8081 h8735 h8736
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6253 hg7338 hg8081 h8735 h8736

end R2N4
