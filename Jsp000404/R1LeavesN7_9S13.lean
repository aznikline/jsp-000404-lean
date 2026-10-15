import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_9S11
import Jsp000404.R1LeavesN7_9S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 14718000 in
set_option maxHeartbeats 14718000 in
theorem r1l7_13_24_L_I_H_I_s0_x1_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h6087 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h6748 | h6748
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6749 | h6749
    · linarith only [h0, h1, h6749, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6751 | h6751
      · linarith only [h0, h6087, h6751, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h6753 | h6753
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6754 | h6754
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6755 | h6755
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6756 | h6756
              · linarith only [h0, h1, h6749, h6756, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6758 | h6758
                · linarith only [h0, h6087, h6751, h6758, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h6760 | h6760
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6761 | h6761
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6762 | h6762
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6763 | h6763
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6764 | h6764
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6765 | h6765
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6766 | h6766
                              · rcases h3bigk with h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c | h6767c
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [hlam, p6767_0]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [h1, hlam, p6767_1]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [h6749, hlam, p6767_1]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  rcases p6767_3 (m.d 0 3) (by simp) with h6771 | h6771
                                  · rcases p6767_3 (m.d 1 3) (by simp) with h6772 | h6772
                                    · rcases p6767_3 (m.d 2 3) (by simp) with h6773 | h6773
                                      · rcases p6767_3 (m.d 3 4) (by simp) with h6774 | h6774
                                        · linarith only [h6774, hlam, p6767_0]
                                        · rcases p6767_3 (m.d 3 5) (by simp) with h6776 | h6776
                                          · linarith only [h6754, h6776, hlam]
                                          · rcases h4bigk with h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [hlam, p6778_0]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [h6087, hlam, p6778_0]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [h6751, hlam, p6778_0]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [h6766, hc04, hc45, hlam, hphi, ht0b, ht5b, p6778_1]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              rcases p6778_3 (m.d 0 4) (by simp) with h6783 | h6783
                                              · rcases p6778_3 (m.d 1 4) (by simp) with h6784 | h6784
                                                · rcases p6778_3 (m.d 2 4) (by simp) with h6785 | h6785
                                                  · rcases p6778_3 (m.d 3 4) (by simp) with h6786 | h6786
                                                    · linarith only [h6753, h6786, hlam]
                                                    · linarith only [h6766, h6786, hlam]
                                                  · linarith only [h6765, h6785, hlam]
                                                · linarith only [h6762, h6784, hlam]
                                              · linarith only [h6783, hlam, p6778_0]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [h6087, h6756, h6760, hc01, hc23, hlam, hphi, ht12, p6778_1]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [hlam, p6778_0]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [h6758, hlam, p6778_0]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [h6756, h6760, h6766, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6778_1]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              rcases p6778_3 (m.d 0 4) (by simp) with h6796 | h6796
                                              · linarith only [h6087, h6796, hlam]
                                              · linarith only [h6755, h6796, hlam]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [h0, h6087, hc12, hc24, hlam, hphi, p6778_1]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [h0, h6087, hc12, hc24, hlam, hphi, p6778_1]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [hlam, p6778_0]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [h6763, h6766, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6778_1]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              rcases p6778_3 (m.d 0 4) (by simp) with h6803 | h6803
                                              · linarith only [h6751, h6803, hlam]
                                              · linarith only [h6755, h6803, hlam]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [h6753, hlam, p6778_1]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [h6760, hlam, p6778_0]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [h6763, hlam, p6778_0]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [hlam, p6778_0]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [hc03, hc45, hlam, hphi, ht0b, ht5b, p6767_1, p6778_1]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [h6755, hlam, p6778_0]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [h6762, hlam, p6778_0]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [h6765, hlam, p6778_0]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [h6766, hlam, p6778_0]
                                            · have p6778_0 := h6778c.1
                                              have p6778_1 := h6778c.2.1
                                              have p6778_2 := h6778c.2.2.1
                                              have p6778_3 := h6778c.2.2.2
                                              linarith only [hlam, p6778_0]
                                      · linarith only [h6763, h6773, hlam]
                                    · linarith only [h6760, h6772, hlam]
                                  · linarith only [h6771, hlam, p6767_0]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  rcases p6767_3 (m.d 0 3) (by simp) with h6819 | h6819
                                  · rcases p6767_3 (m.d 1 3) (by simp) with h6820 | h6820
                                    · rcases p6767_3 (m.d 2 3) (by simp) with h6821 | h6821
                                      · rcases p6767_3 (m.d 3 4) (by simp) with h6822 | h6822
                                        · linarith only [h6753, h6822, hlam]
                                        · linarith only [h6766, h6822, hlam]
                                      · linarith only [h6764, h6821, hlam]
                                    · linarith only [h6761, h6820, hlam]
                                  · linarith only [h6819, hlam, p6767_0]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [h0, h1, h6756, hc12, hc23, hlam, hphi, p6767_1]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [hlam, p6767_0]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [h6756, hlam, p6767_1]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  rcases p6767_3 (m.d 0 3) (by simp) with h6831 | h6831
                                  · linarith only [h1, h6831, hlam]
                                  · linarith only [h6753, h6831, hlam]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  rcases p6767_3 (m.d 0 3) (by simp) with h6834 | h6834
                                  · linarith only [h1, h6834, hlam]
                                  · linarith only [h6754, h6834, hlam]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [h0, h1, hc12, hc23, hlam, hphi, p6767_1]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [h0, h1, hc12, hc23, hlam, hphi, p6767_1]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [hlam, p6767_0]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  rcases p6767_3 (m.d 0 3) (by simp) with h6840 | h6840
                                  · linarith only [h6749, h6840, hlam]
                                  · linarith only [h6753, h6840, hlam]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  rcases p6767_3 (m.d 0 3) (by simp) with h6843 | h6843
                                  · linarith only [h6749, h6843, hlam]
                                  · linarith only [h6754, h6843, hlam]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [h6753, hlam, p6767_0]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [h6760, hlam, p6767_0]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [h6763, hlam, p6767_0]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [hlam, p6767_0]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  rcases p6767_3 (m.d 0 3) (by simp) with h6850 | h6850
                                  · rcases p6767_3 (m.d 1 3) (by simp) with h6851 | h6851
                                    · rcases p6767_3 (m.d 2 3) (by simp) with h6852 | h6852
                                      · rcases p6767_3 (m.d 3 4) (by simp) with h6853 | h6853
                                        · rcases p6767_3 (m.d 3 5) (by simp) with h6854 | h6854
                                          · linarith only [h6766, h6854, hlam]
                                          · rcases h4bigk with h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c | h6856c
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [hlam, p6856_0]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [h6087, hlam, p6856_0]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [h6751, hlam, p6856_0]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [hc04, hc35, hlam, hphi, ht0b, ht5b, p6767_1, p6856_1]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              rcases p6856_3 (m.d 0 4) (by simp) with h6861 | h6861
                                              · rcases p6856_3 (m.d 1 4) (by simp) with h6862 | h6862
                                                · rcases p6856_3 (m.d 2 4) (by simp) with h6863 | h6863
                                                  · rcases p6856_3 (m.d 3 4) (by simp) with h6864 | h6864
                                                    · linarith only [h6753, h6864, hlam]
                                                    · linarith only [h6766, h6864, hlam]
                                                  · linarith only [h6765, h6863, hlam]
                                                · linarith only [h6762, h6862, hlam]
                                              · linarith only [h6861, hlam, p6856_0]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [h0, h6087, h6758, h6763, hc12, hc23, hlam, hphi, p6856_1]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [hlam, p6856_0]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [h6758, hlam, p6856_0]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [h6758, h6763, h6766, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6767_1, p6856_1]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              rcases p6856_3 (m.d 0 4) (by simp) with h6874 | h6874
                                              · linarith only [h6087, h6874, hlam]
                                              · linarith only [h6755, h6874, hlam]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [h6753, h6763, h6766, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6767_1, p6856_1]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [h0, h6087, h6763, hc12, hc23, hlam, hphi, p6856_1]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [hlam, p6856_0]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [h6763, h6766, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6767_1, p6856_1]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              rcases p6856_3 (m.d 0 4) (by simp) with h6881 | h6881
                                              · linarith only [h6751, h6881, hlam]
                                              · linarith only [h6755, h6881, hlam]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [h6753, hlam, p6856_1]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [h6760, hlam, p6856_0]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [h6763, hlam, p6856_0]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [hlam, p6856_0]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [h1, h6753, h6756, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6856_1]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [h6755, hlam, p6856_0]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [h6762, hlam, p6856_0]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [h6765, hlam, p6856_0]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [h6766, hlam, p6856_0]
                                            · have p6856_0 := h6856c.1
                                              have p6856_1 := h6856c.2.1
                                              have p6856_2 := h6856c.2.2.1
                                              have p6856_3 := h6856c.2.2.2
                                              linarith only [hlam, p6856_0]
                                        · linarith only [h6766, h6853, hlam]
                                      · linarith only [h6764, h6852, hlam]
                                    · linarith only [h6761, h6851, hlam]
                                  · linarith only [h6754, h6850, hlam]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [h6754, hlam, p6767_0]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [h6761, hlam, p6767_0]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [h6764, hlam, p6767_0]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [h6766, hlam, p6767_0]
                                · have p6767_0 := h6767c.1
                                  have p6767_1 := h6767c.2.1
                                  have p6767_2 := h6767c.2.2.1
                                  have p6767_3 := h6767c.2.2.2
                                  linarith only [hlam, p6767_0]
                              · rcases h3bigk with h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c | h6903c
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [hlam, p6903_0]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [h1, hlam, p6903_1]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [h6749, hlam, p6903_1]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  rcases p6903_3 (m.d 0 3) (by simp) with h6907 | h6907
                                  · rcases p6903_3 (m.d 1 3) (by simp) with h6908 | h6908
                                    · rcases p6903_3 (m.d 2 3) (by simp) with h6909 | h6909
                                      · rcases p6903_3 (m.d 3 4) (by simp) with h6910 | h6910
                                        · linarith only [h6910, hlam, p6903_0]
                                        · rcases p6903_3 (m.d 3 5) (by simp) with h6912 | h6912
                                          · linarith only [h6754, h6912, hlam]
                                          · linarith only [h6766, h6912, hlam]
                                      · linarith only [h6763, h6909, hlam]
                                    · linarith only [h6760, h6908, hlam]
                                  · linarith only [h6907, hlam, p6903_0]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  rcases p6903_3 (m.d 0 3) (by simp) with h6918 | h6918
                                  · rcases p6903_3 (m.d 1 3) (by simp) with h6919 | h6919
                                    · rcases p6903_3 (m.d 2 3) (by simp) with h6920 | h6920
                                      · rcases p6903_3 (m.d 3 4) (by simp) with h6921 | h6921
                                        · linarith only [h6753, h6921, hlam]
                                        · rcases p6903_3 (m.d 3 5) (by simp) with h6923 | h6923
                                          · linarith only [h6923, hlam, p6903_0]
                                          · rcases h4bigk with h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c | h6925c
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [hlam, p6925_0]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [h6087, hlam, p6925_0]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [h6751, hlam, p6925_0]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              rcases p6925_3 (m.d 0 4) (by simp) with h6929 | h6929
                                              · rcases p6925_3 (m.d 1 4) (by simp) with h6930 | h6930
                                                · rcases p6925_3 (m.d 2 4) (by simp) with h6931 | h6931
                                                  · rcases p6925_3 (m.d 3 4) (by simp) with h6932 | h6932
                                                    · linarith only [h6753, h6932, hlam]
                                                    · rcases p6925_3 (m.d 4 5) (by simp) with h6934 | h6934
                                                      · linarith only [h6755, h6934, hlam]
                                                      · linarith only [h6766, h6934, hlam]
                                                  · linarith only [h6763, h6931, hlam]
                                                · linarith only [h6760, h6930, hlam]
                                              · linarith only [h6753, h6929, hlam]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [h6753, h6766, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p6925_1]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [h6087, h6748, h6762, h6766, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6925_1]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [hlam, p6925_0]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [h6758, hlam, p6925_0]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              rcases p6925_3 (m.d 0 4) (by simp) with h6944 | h6944
                                              · linarith only [h6087, h6944, hlam]
                                              · linarith only [h6753, h6944, hlam]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [h6758, h6763, h6766, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6925_1]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [h6087, h6748, h6762, h6763, h6766, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6925_1]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [h6087, h6748, h6762, h6763, h6766, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6925_1]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [hlam, p6925_0]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              rcases p6925_3 (m.d 0 4) (by simp) with h6951 | h6951
                                              · linarith only [h6751, h6951, hlam]
                                              · linarith only [h6753, h6951, hlam]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [h6763, h6766, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6925_1]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [h6753, hlam, p6925_1]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [h6760, hlam, p6925_0]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [h6763, hlam, p6925_0]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [hlam, p6925_0]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [h6766, hlam, p6925_0]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [h6755, hlam, p6925_0]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [h6762, hlam, p6925_0]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [h6765, hlam, p6925_0]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [h6748, h6762, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6925_1]
                                            · have p6925_0 := h6925c.1
                                              have p6925_1 := h6925c.2.1
                                              have p6925_2 := h6925c.2.2.1
                                              have p6925_3 := h6925c.2.2.2
                                              linarith only [hlam, p6925_0]
                                      · linarith only [h6764, h6920, hlam]
                                    · linarith only [h6761, h6919, hlam]
                                  · linarith only [h6918, hlam, p6903_0]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [h0, h1, h6756, hc12, hc23, hlam, hphi, p6903_1]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [hlam, p6903_0]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [h6756, hlam, p6903_1]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [h1, h6748, h6762, h6766, hlam, p6903_2]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  rcases p6903_3 (m.d 0 3) (by simp) with h6972 | h6972
                                  · linarith only [h1, h6972, hlam]
                                  · linarith only [h6754, h6972, hlam]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [h1, h6748, h6762, h6766, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6903_1]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [h1, h6748, h6762, h6766, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6903_1]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [hlam, p6903_0]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [h6087, h6748, h6758, h6762, h6763, h6766, hlam, p6903_2]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  rcases p6903_3 (m.d 0 3) (by simp) with h6979 | h6979
                                  · linarith only [h6749, h6979, hlam]
                                  · linarith only [h6754, h6979, hlam]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [h6753, hlam, p6903_0]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [h6760, hlam, p6903_0]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [h6763, hlam, p6903_0]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [hlam, p6903_0]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [h6766, hlam, p6903_1]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [h6754, hlam, p6903_0]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [h6761, hlam, p6903_0]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [h6764, hlam, p6903_0]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [h6087, h6748, h6760, h6761, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6903_1]
                                · have p6903_0 := h6903c.1
                                  have p6903_1 := h6903c.2.1
                                  have p6903_2 := h6903c.2.2.1
                                  have p6903_3 := h6903c.2.2.2
                                  linarith only [hlam, p6903_0]
                            · linarith only [h6751, h6755, h6765, hlam]
                          · linarith only [h6087, h6748, h6756, h6760, h6761, h6764, hlam]
                        · linarith only [h0, h6087, h6756, h6760, h6763, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h6087, h6762, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h0, h6087, h6760, h6761, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h6753, h6760, hlam]
            · linarith only [h6087, h6748, h6755, hlam]
          · linarith only [h1, h6748, h6754, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h7000 | h7000
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7001 | h7001
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7002 | h7002
              · linarith only [h0, h1, h6753, h7002, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7004 | h7004
                · linarith only [h0, h1, h6751, h6753, h7004, hc02, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7006 | h7006
                  · linarith only [h0, h1, h6753, h7002, h7006, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h7006, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h6748, h6753, h7001, hlam]
          · linarith only [h1, h6748, h7000, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h7011 | h7011
    · linarith only [h0, h1, h7011, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h7013 | h7013
      · linarith only [h0, h6087, h7013, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h7015 | h7015
        · rcases m.htr 0 3 5 (by decide) (by decide) with h7016 | h7016
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7017 | h7017
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7018 | h7018
              · linarith only [h0, h1, h7011, h7018, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7020 | h7020
                · linarith only [h0, h6748, h7013, h7017, h7020, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7022 | h7022
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7023 | h7023
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h7024 | h7024
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7025 | h7025
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7026 | h7026
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7027 | h7027
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7028 | h7028
                              · rcases h3bigk with h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c | h7029c
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [hlam, p7029_0]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [h1, hlam, p7029_1]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [h7011, hlam, p7029_1]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  rcases p7029_3 (m.d 0 3) (by simp) with h7033 | h7033
                                  · rcases p7029_3 (m.d 1 3) (by simp) with h7034 | h7034
                                    · rcases p7029_3 (m.d 2 3) (by simp) with h7035 | h7035
                                      · rcases p7029_3 (m.d 3 4) (by simp) with h7036 | h7036
                                        · linarith only [h7036, hlam, p7029_0]
                                        · rcases p7029_3 (m.d 3 5) (by simp) with h7038 | h7038
                                          · linarith only [h7016, h7038, hlam]
                                          · rcases h4bigk with h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c | h7040c
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [hlam, p7040_0]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [h6087, hlam, p7040_0]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [h7013, hlam, p7040_0]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [h7028, hc04, hc45, hlam, hphi, ht0b, ht5b, p7040_1]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              rcases p7040_3 (m.d 0 4) (by simp) with h7045 | h7045
                                              · rcases p7040_3 (m.d 1 4) (by simp) with h7046 | h7046
                                                · rcases p7040_3 (m.d 2 4) (by simp) with h7047 | h7047
                                                  · rcases p7040_3 (m.d 3 4) (by simp) with h7048 | h7048
                                                    · linarith only [h7015, h7048, hlam]
                                                    · linarith only [h7028, h7048, hlam]
                                                  · linarith only [h7027, h7047, hlam]
                                                · linarith only [h7024, h7046, hlam]
                                              · linarith only [h7045, hlam, p7040_0]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [h6087, h7018, h7022, hc01, hc23, hlam, hphi, ht12, p7040_1]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [hlam, p7040_0]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [h7020, hlam, p7040_0]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [h7018, h7022, h7028, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7040_1]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              rcases p7040_3 (m.d 0 4) (by simp) with h7058 | h7058
                                              · linarith only [h6087, h7058, hlam]
                                              · linarith only [h7017, h7058, hlam]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [h0, h6748, h7017, hc12, hc24, hlam, hphi, p7040_1]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [h0, h6087, hc12, hc24, hlam, hphi, p7040_1]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [hlam, p7040_0]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [h7025, h7028, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7040_1]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              rcases p7040_3 (m.d 0 4) (by simp) with h7065 | h7065
                                              · linarith only [h7013, h7065, hlam]
                                              · linarith only [h7017, h7065, hlam]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [h7015, hlam, p7040_1]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [h7022, hlam, p7040_0]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [h7025, hlam, p7040_0]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [hlam, p7040_0]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [hc03, hc45, hlam, hphi, ht0b, ht5b, p7029_1, p7040_1]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [h7017, hlam, p7040_0]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [h7024, hlam, p7040_0]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [h7027, hlam, p7040_0]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [h7028, hlam, p7040_0]
                                            · have p7040_0 := h7040c.1
                                              have p7040_1 := h7040c.2.1
                                              have p7040_2 := h7040c.2.2.1
                                              have p7040_3 := h7040c.2.2.2
                                              linarith only [hlam, p7040_0]
                                      · linarith only [h7025, h7035, hlam]
                                    · linarith only [h7022, h7034, hlam]
                                  · linarith only [h7033, hlam, p7029_0]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  rcases p7029_3 (m.d 0 3) (by simp) with h7081 | h7081
                                  · rcases p7029_3 (m.d 1 3) (by simp) with h7082 | h7082
                                    · rcases p7029_3 (m.d 2 3) (by simp) with h7083 | h7083
                                      · rcases p7029_3 (m.d 3 4) (by simp) with h7084 | h7084
                                        · linarith only [h7015, h7084, hlam]
                                        · linarith only [h7028, h7084, hlam]
                                      · linarith only [h7026, h7083, hlam]
                                    · linarith only [h7023, h7082, hlam]
                                  · linarith only [h7081, hlam, p7029_0]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [h0, h1, h7018, hc12, hc23, hlam, hphi, p7029_1]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [hlam, p7029_0]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [h7018, hlam, p7029_1]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  rcases p7029_3 (m.d 0 3) (by simp) with h7093 | h7093
                                  · linarith only [h1, h7093, hlam]
                                  · linarith only [h7015, h7093, hlam]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  rcases p7029_3 (m.d 0 3) (by simp) with h7096 | h7096
                                  · linarith only [h1, h7096, hlam]
                                  · linarith only [h7016, h7096, hlam]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [h0, h6748, h7015, h7017, hc12, hc23, hlam, hphi, p7029_1]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [h0, h1, hc12, hc23, hlam, hphi, p7029_1]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [hlam, p7029_0]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  rcases p7029_3 (m.d 0 3) (by simp) with h7102 | h7102
                                  · linarith only [h7011, h7102, hlam]
                                  · linarith only [h7015, h7102, hlam]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  rcases p7029_3 (m.d 0 3) (by simp) with h7105 | h7105
                                  · linarith only [h7011, h7105, hlam]
                                  · linarith only [h7016, h7105, hlam]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [h7015, hlam, p7029_0]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [h7022, hlam, p7029_0]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [h7025, hlam, p7029_0]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [hlam, p7029_0]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  rcases p7029_3 (m.d 0 3) (by simp) with h7112 | h7112
                                  · rcases p7029_3 (m.d 1 3) (by simp) with h7113 | h7113
                                    · rcases p7029_3 (m.d 2 3) (by simp) with h7114 | h7114
                                      · rcases p7029_3 (m.d 3 4) (by simp) with h7115 | h7115
                                        · rcases p7029_3 (m.d 3 5) (by simp) with h7116 | h7116
                                          · linarith only [h7028, h7116, hlam]
                                          · rcases h4bigk with h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c | h7118c
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [hlam, p7118_0]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [h6087, hlam, p7118_0]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [h7013, hlam, p7118_0]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [h7028, hc04, hc45, hlam, hphi, ht0b, ht5b, p7029_1, p7118_1]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              rcases p7118_3 (m.d 0 4) (by simp) with h7123 | h7123
                                              · rcases p7118_3 (m.d 1 4) (by simp) with h7124 | h7124
                                                · rcases p7118_3 (m.d 2 4) (by simp) with h7125 | h7125
                                                  · rcases p7118_3 (m.d 3 4) (by simp) with h7126 | h7126
                                                    · linarith only [h7015, h7126, hlam]
                                                    · linarith only [h7028, h7126, hlam]
                                                  · linarith only [h7027, h7125, hlam]
                                                · linarith only [h7024, h7124, hlam]
                                              · linarith only [h7123, hlam, p7118_0]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [h0, h6087, h7022, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7118_1]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [hlam, p7118_0]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [h7020, hlam, p7118_0]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [h7018, h7022, h7028, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7029_1, p7118_1]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              rcases p7118_3 (m.d 0 4) (by simp) with h7136 | h7136
                                              · linarith only [h6087, h7136, hlam]
                                              · linarith only [h7017, h7136, hlam]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [h7015, h7025, h7028, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7029_1, p7118_1]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [h0, h6087, h7025, hc12, hc23, hlam, hphi, p7118_1]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [hlam, p7118_0]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [h7025, h7028, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7029_1, p7118_1]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              rcases p7118_3 (m.d 0 4) (by simp) with h7143 | h7143
                                              · linarith only [h7013, h7143, hlam]
                                              · linarith only [h7017, h7143, hlam]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [h7015, hlam, p7118_1]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [h7022, hlam, p7118_0]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [h7025, hlam, p7118_0]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [hlam, p7118_0]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [h7015, hc03, hc45, hlam, hphi, ht0b, ht5b, p7118_1]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [h7017, hlam, p7118_0]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [h7024, hlam, p7118_0]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [h7027, hlam, p7118_0]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [h7028, hlam, p7118_0]
                                            · have p7118_0 := h7118c.1
                                              have p7118_1 := h7118c.2.1
                                              have p7118_2 := h7118c.2.2.1
                                              have p7118_3 := h7118c.2.2.2
                                              linarith only [hlam, p7118_0]
                                        · linarith only [h7028, h7115, hlam]
                                      · linarith only [h7026, h7114, hlam]
                                    · linarith only [h7023, h7113, hlam]
                                  · linarith only [h7016, h7112, hlam]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [h7016, hlam, p7029_0]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [h7023, hlam, p7029_0]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [h7026, hlam, p7029_0]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [h7028, hlam, p7029_0]
                                · have p7029_0 := h7029c.1
                                  have p7029_1 := h7029c.2.1
                                  have p7029_2 := h7029c.2.2.1
                                  have p7029_3 := h7029c.2.2.2
                                  linarith only [hlam, p7029_0]
                              · rcases h3bigk with h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c | h7165c
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [hlam, p7165_0]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [h1, hlam, p7165_1]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [h7011, hlam, p7165_1]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  rcases p7165_3 (m.d 0 3) (by simp) with h7169 | h7169
                                  · rcases p7165_3 (m.d 1 3) (by simp) with h7170 | h7170
                                    · rcases p7165_3 (m.d 2 3) (by simp) with h7171 | h7171
                                      · rcases p7165_3 (m.d 3 4) (by simp) with h7172 | h7172
                                        · linarith only [h7172, hlam, p7165_0]
                                        · rcases p7165_3 (m.d 3 5) (by simp) with h7174 | h7174
                                          · linarith only [h7016, h7174, hlam]
                                          · linarith only [h7028, h7174, hlam]
                                      · linarith only [h7025, h7171, hlam]
                                    · linarith only [h7022, h7170, hlam]
                                  · linarith only [h7169, hlam, p7165_0]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  rcases p7165_3 (m.d 0 3) (by simp) with h7180 | h7180
                                  · rcases p7165_3 (m.d 1 3) (by simp) with h7181 | h7181
                                    · rcases p7165_3 (m.d 2 3) (by simp) with h7182 | h7182
                                      · rcases p7165_3 (m.d 3 4) (by simp) with h7183 | h7183
                                        · linarith only [h7015, h7183, hlam]
                                        · rcases p7165_3 (m.d 3 5) (by simp) with h7185 | h7185
                                          · linarith only [h7185, hlam, p7165_0]
                                          · rcases h4bigk with h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c | h7187c
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [hlam, p7187_0]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [h6087, hlam, p7187_0]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [h7013, hlam, p7187_0]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              rcases p7187_3 (m.d 0 4) (by simp) with h7191 | h7191
                                              · rcases p7187_3 (m.d 1 4) (by simp) with h7192 | h7192
                                                · rcases p7187_3 (m.d 2 4) (by simp) with h7193 | h7193
                                                  · rcases p7187_3 (m.d 3 4) (by simp) with h7194 | h7194
                                                    · linarith only [h7015, h7194, hlam]
                                                    · rcases p7187_3 (m.d 4 5) (by simp) with h7196 | h7196
                                                      · linarith only [h7017, h7196, hlam]
                                                      · linarith only [h7028, h7196, hlam]
                                                  · linarith only [h7025, h7193, hlam]
                                                · linarith only [h7022, h7192, hlam]
                                              · linarith only [h7015, h7191, hlam]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [h7015, h7028, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7187_1]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [h0, h6087, h7020, h7025, hc12, hc23, hlam, hphi, p7187_1]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [hlam, p7187_0]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [h7020, hlam, p7187_0]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              rcases p7187_3 (m.d 0 4) (by simp) with h7206 | h7206
                                              · linarith only [h6087, h7206, hlam]
                                              · linarith only [h7015, h7206, hlam]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [h7020, h7025, h7028, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7187_1]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [h7017, h7025, h7028, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7187_1]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [h0, h6087, h7025, hc12, hc23, hlam, hphi, p7187_1]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [hlam, p7187_0]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              rcases p7187_3 (m.d 0 4) (by simp) with h7213 | h7213
                                              · linarith only [h7013, h7213, hlam]
                                              · linarith only [h7015, h7213, hlam]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [h7025, h7028, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7187_1]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [h7015, hlam, p7187_1]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [h7022, hlam, p7187_0]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [h7025, hlam, p7187_0]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [hlam, p7187_0]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [h7028, hlam, p7187_0]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [h7017, hlam, p7187_0]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [h7024, hlam, p7187_0]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [h7027, hlam, p7187_0]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [h7017, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p7187_1]
                                            · have p7187_0 := h7187c.1
                                              have p7187_1 := h7187c.2.1
                                              have p7187_2 := h7187c.2.2.1
                                              have p7187_3 := h7187c.2.2.2
                                              linarith only [hlam, p7187_0]
                                      · linarith only [h7026, h7182, hlam]
                                    · linarith only [h7023, h7181, hlam]
                                  · linarith only [h7180, hlam, p7165_0]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [h0, h1, h7018, hc12, hc23, hlam, hphi, p7165_1]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [hlam, p7165_0]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [h7018, hlam, p7165_1]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  rcases p7165_3 (m.d 0 3) (by simp) with h7233 | h7233
                                  · linarith only [h1, h7233, hlam]
                                  · linarith only [h7015, h7233, hlam]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  rcases p7165_3 (m.d 0 3) (by simp) with h7236 | h7236
                                  · linarith only [h1, h7236, hlam]
                                  · linarith only [h7016, h7236, hlam]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [h0, h1, hc12, hc23, hlam, hphi, p7165_1]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [h0, h1, hc12, hc23, hlam, hphi, p7165_1]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [hlam, p7165_0]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  rcases p7165_3 (m.d 0 3) (by simp) with h7242 | h7242
                                  · linarith only [h7011, h7242, hlam]
                                  · linarith only [h7015, h7242, hlam]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  rcases p7165_3 (m.d 0 3) (by simp) with h7245 | h7245
                                  · linarith only [h7011, h7245, hlam]
                                  · linarith only [h7016, h7245, hlam]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [h7015, hlam, p7165_0]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [h7022, hlam, p7165_0]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [h7025, hlam, p7165_0]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [hlam, p7165_0]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [h7028, hlam, p7165_1]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [h7016, hlam, p7165_0]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [h7023, hlam, p7165_0]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [h7026, hlam, p7165_0]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  rcases p7165_3 (m.d 0 3) (by simp) with h7256 | h7256
                                  · rcases p7165_3 (m.d 1 3) (by simp) with h7257 | h7257
                                    · rcases p7165_3 (m.d 2 3) (by simp) with h7258 | h7258
                                      · rcases p7165_3 (m.d 3 4) (by simp) with h7259 | h7259
                                        · linarith only [h7028, h7259, hlam]
                                        · rcases p7165_3 (m.d 3 5) (by simp) with h7261 | h7261
                                          · rcases h4bigk with h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c | h7262c
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [hlam, p7262_0]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [h6087, hlam, p7262_0]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [h7013, hlam, p7262_0]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              rcases p7262_3 (m.d 0 4) (by simp) with h7266 | h7266
                                              · rcases p7262_3 (m.d 1 4) (by simp) with h7267 | h7267
                                                · rcases p7262_3 (m.d 2 4) (by simp) with h7268 | h7268
                                                  · rcases p7262_3 (m.d 3 4) (by simp) with h7269 | h7269
                                                    · linarith only [h7015, h7269, hlam]
                                                    · rcases p7262_3 (m.d 4 5) (by simp) with h7271 | h7271
                                                      · linarith only [h7017, h7271, hlam]
                                                      · linarith only [h7028, h7271, hlam]
                                                  · linarith only [h7025, h7268, hlam]
                                                · linarith only [h7022, h7267, hlam]
                                              · linarith only [h7015, h7266, hlam]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [h6087, h7020, h7025, h7028, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7165_1, p7262_1]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [h0, h6087, h7020, h7025, hc12, hc23, hlam, hphi, p7262_1]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [hlam, p7262_0]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [h7020, hlam, p7262_0]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              rcases p7262_3 (m.d 0 4) (by simp) with h7281 | h7281
                                              · linarith only [h6087, h7281, hlam]
                                              · linarith only [h7015, h7281, hlam]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [h7020, h7025, h7028, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7165_1, p7262_1]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [h7017, h7025, h7028, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7165_1, p7262_1]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [h0, h6087, h7025, hc12, hc23, hlam, hphi, p7262_1]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [hlam, p7262_0]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              rcases p7262_3 (m.d 0 4) (by simp) with h7288 | h7288
                                              · linarith only [h7013, h7288, hlam]
                                              · linarith only [h7015, h7288, hlam]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [h7025, h7028, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7165_1, p7262_1]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [h7015, hlam, p7262_1]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [h7022, hlam, p7262_0]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [h7025, hlam, p7262_0]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [hlam, p7262_0]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [h7028, hlam, p7262_0]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [h7017, hlam, p7262_0]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [h7024, hlam, p7262_0]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [h7027, hlam, p7262_0]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [h7017, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p7262_1]
                                            · have p7262_0 := h7262c.1
                                              have p7262_1 := h7262c.2.1
                                              have p7262_2 := h7262c.2.2.1
                                              have p7262_3 := h7262c.2.2.2
                                              linarith only [hlam, p7262_0]
                                          · linarith only [h7028, h7261, hlam]
                                      · linarith only [h7025, h7258, hlam]
                                    · linarith only [h7022, h7257, hlam]
                                  · linarith only [h7015, h7256, hlam]
                                · have p7165_0 := h7165c.1
                                  have p7165_1 := h7165c.2.1
                                  have p7165_2 := h7165c.2.2.1
                                  have p7165_3 := h7165c.2.2.2
                                  linarith only [hlam, p7165_0]
                            · linarith only [h0, h1, h6087, h7015, h7017, h7018, h7020, h7027, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h7018, h7026, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h7018, h7025, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h6087, h7015, h7017, h7024, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h1, h7016, h7023, hlam]
                  · linarith only [h1, h7015, h7022, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7313 | h7313
              · linarith only [h0, h6087, h7017, h7313, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7315 | h7315
                · linarith only [h0, h6087, h7017, h7315, hc24, hc45, hlam, hphi]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7317 | h7317
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7318 | h7318
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h7319 | h7319
                      · linarith only [h0, h6087, h7017, h7315, h7319, hc12, hc24, hlam, hphi]
                      · linarith only [h0, h6087, h7319, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h1, h7016, h7318, hlam]
                  · linarith only [h0, h1, h7015, h7017, h7317, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7324 | h7324
            · linarith only [h7015, h7016, h7324, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7326 | h7326
              · linarith only [h0, h6087, h7324, h7326, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7328 | h7328
                · linarith only [h0, h6087, h7324, h7328, hc24, hc45, hlam, hphi]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7330 | h7330
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7331 | h7331
                    · linarith only [h0, h6087, h7015, h7016, h7326, h7331, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h7331, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h0, h1, h7015, h7016, h7330, hc12, hc35, hlam, hphi, ht23]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h7335 | h7335
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7336 | h7336
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7337 | h7337
              · linarith only [h0, h1, h7015, h7337, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7339 | h7339
                · linarith only [h0, h7013, h7339, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7341 | h7341
                  · linarith only [h0, h6748, h7015, h7335, h7337, h7341, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h7341, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h7015, h7335, h7336, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7345 | h7345
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7346 | h7346
              · linarith only [h0, h1, h7335, h7346, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7348 | h7348
                · linarith only [h0, h7013, h7348, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7350 | h7350
                  · linarith only [h0, h1, h7015, h7346, h7350, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h7350, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7353 | h7353
              · linarith only [h0, h1, h7015, h7345, h7353, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7355 | h7355
                · linarith only [h0, h1, h7013, h7015, h7355, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7357 | h7357
                  · linarith only [h0, h1, h7015, h7353, h7357, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h7357, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 14718000 in
set_option maxHeartbeats 14718000 in
theorem r1l7_13_24_L_I_H_I_s0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h6087 | h6087
  · exact r1l7_13_24_L_I_H_I_s0_x1_x0 m hb3 hb4 hg0 h1 h6087
  · exact r1l7_13_24_L_I_H_I_s0_x1_x1 m hb3 hb4 hg0 h1 h6087

set_option maxHeartbeats 14718000 in
set_option maxHeartbeats 14718000 in
theorem r1l7_13_24_L_I_H_I_s0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_13_24_L_I_H_I_s0_x0 m hb3 hb4 hg0 h1
  · exact r1l7_13_24_L_I_H_I_s0_x1 m hb3 hb4 hg0 h1

end R2N4
