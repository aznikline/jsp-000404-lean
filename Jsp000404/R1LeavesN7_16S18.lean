import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_16S9
import Jsp000404.R1LeavesN7_16S16
import Jsp000404.R1LeavesN7_16S17

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10428000 in
set_option maxHeartbeats 10428000 in
theorem r1l7_21_15_H_I_L_I_s7_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6137 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h6138 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h6780 | h6780
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6781 | h6781
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6782 | h6782
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6783 | h6783
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6784 | h6784
          · linarith only [h6137, h6138, h6784, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6786 | h6786
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6787 | h6787
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6788 | h6788
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6789 | h6789
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6790 | h6790
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6791 | h6791
                      · linarith only [h6137, h6138, h6784, h6789, h6791, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6793 | h6793
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6794 | h6794
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6795 | h6795
                            · linarith only [h6137, h6138, h6788, h6791, h6795, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6797 | h6797
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6798 | h6798
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6799 | h6799
                                  · rcases h1bigk with h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c | h6800c
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [hlam, p6800_0]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [h0, hlam, p6800_0]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [h6138, h6791, hc13, hc34, hlam, hphi, p6800_1]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [h6138, hlam, p6800_0]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [h6138, h6791, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6800_1]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p6800_1]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [hlam, p6800_0]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [h6788, h6797, h6799, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6800_1]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [h6137, h6138, h6788, h6797, h6799, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6800_1]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      rcases p6800_3 (m.d 0 1) (by simp) with h6810 | h6810
                                      · linarith only [h0, h6810, hlam]
                                      · linarith only [h6780, h6810, hlam]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [h6137, hlam, p6800_0]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [h6788, hlam, p6800_1]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [hlam, p6800_0]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [h6791, hlam, p6800_1]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [h6137, hc01, hc15, hlam, hphi, ht0b, ht5b, p6800_1]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [hc01, hc14, hlam, hphi, p6800_1]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [h6789, hlam, p6800_1]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [h6788, h6791, h6797, h6799, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6800_1]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [hlam, p6800_0]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      rcases p6800_3 (m.d 0 1) (by simp) with h6822 | h6822
                                      · linarith only [h6138, h6822, hlam]
                                      · linarith only [h6780, h6822, hlam]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [h6780, hlam, p6800_0]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [h6790, hlam, p6800_1]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [h6793, hlam, p6800_0]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [h6794, hlam, p6800_0]
                                    · have p6800_0 := h6800c.1
                                      have p6800_1 := h6800c.2.1
                                      have p6800_2 := h6800c.2.2.1
                                      have p6800_3 := h6800c.2.2.2
                                      linarith only [hlam, p6800_0]
                                  · linarith only [h6137, h6138, h6791, h6799, hc13, hc45, hlam, hphi, ht34]
                                · linarith only [h6137, h6138, h6791, h6793, h6794, h6795, h6797, h6798, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h6137, h6138, h6786, h6791, h6797, hc23, hc34, hlam, hphi]
                          · linarith only [h6137, h6138, h6794, hc13, hc45, hlam, hphi, ht34]
                        · linarith only [h6137, h6138, h6786, h6791, h6793, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h6783, h6790, hlam]
                  · linarith only [h0, h6782, h6789, hlam]
                · linarith only [h0, h6781, h6788, hlam]
              · linarith only [h6138, h6780, h6787, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6839 | h6839
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6840 | h6840
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6841 | h6841
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6842 | h6842
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6843 | h6843
                      · linarith only [h6137, h6138, h6784, h6841, h6843, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6845 | h6845
                        · linarith only [h6137, h6786, h6845, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6847 | h6847
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6848 | h6848
                            · linarith only [h6137, h6138, h6786, h6840, h6843, h6848, hc01, hc35, hlam, hphi, ht12, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6850 | h6850
                              · linarith only [h6138, h6780, h6786, h6840, h6843, h6845, h6850, hc03, hc34, hlam, hphi]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6852 | h6852
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6853 | h6853
                                  · rcases h1bigk with h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c | h6854c
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [hlam, p6854_0]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [h0, hlam, p6854_0]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [h6138, h6843, hc13, hc34, hlam, hphi, p6854_1]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [h6138, hlam, p6854_0]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [h6138, h6843, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6854_1]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p6854_1]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [hlam, p6854_0]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      rcases p6854_3 (m.d 0 1) (by simp) with h6862 | h6862
                                      · linarith only [h0, h6862, hlam]
                                      · linarith only [h6137, h6862, hlam]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [h6138, hc01, hc12, hlam, hphi, p6854_1]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      rcases p6854_3 (m.d 0 1) (by simp) with h6866 | h6866
                                      · linarith only [h0, h6866, hlam]
                                      · linarith only [h6780, h6866, hlam]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [h6137, hlam, p6854_0]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [h6840, hlam, p6854_1]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [hlam, p6854_0]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [h6843, hlam, p6854_1]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [h6845, hlam, p6854_1]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [h6780, h6842, h6850, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6854_1]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [h6841, hlam, p6854_1]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [h6840, h6843, hc23, hc34, hlam, hphi, p6854_1]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [hlam, p6854_0]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [h6842, h6843, h6850, hc23, hc34, hlam, hphi, p6854_1]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [h6780, hlam, p6854_0]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [h6842, hlam, p6854_1]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [h6780, h6840, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6854_1]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [h6847, hlam, p6854_0]
                                    · have p6854_0 := h6854c.1
                                      have p6854_1 := h6854c.2.1
                                      have p6854_2 := h6854c.2.2.1
                                      have p6854_3 := h6854c.2.2.2
                                      linarith only [hlam, p6854_0]
                                  · linarith only [h6138, h6780, h6842, h6843, h6852, h6853, hlam]
                                · linarith only [h6138, h6780, h6843, h6847, h6848, h6852, hc23, hc34, hlam, hphi]
                          · linarith only [h6137, h6138, h6840, h6847, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6783, h6842, hlam]
                  · linarith only [h0, h6782, h6841, hlam]
                · linarith only [h0, h6781, h6840, hlam]
              · linarith only [h6138, h6780, h6839, hlam]
        · linarith only [h0, h6780, h6783, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6892 | h6892
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6893 | h6893
          · linarith only [h0, h6137, h6782, h6893, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6895 | h6895
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6896 | h6896
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6897 | h6897
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6898 | h6898
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6899 | h6899
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6900 | h6900
                      · linarith only [h0, h6137, h6782, h6893, h6898, h6900, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6902 | h6902
                        · linarith only [h0, h6137, h6782, h6898, h6902, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h6137, h6782, h6895, h6897, h6898, h6902, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h6782, h6898, h6899, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6906 | h6906
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6907 | h6907
                      · linarith only [h0, h6137, h6782, h6893, h6898, h6907, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6909 | h6909
                        · linarith only [h0, h6137, h6898, h6909, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h6137, h6895, h6898, h6909, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h6780, h6782, h6892, h6906, hc04, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h6781, h6897, hlam]
              · linarith only [h0, h6137, h6782, h6895, h6896, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6915 | h6915
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6916 | h6916
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6917 | h6917
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6918 | h6918
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6919 | h6919
                      · linarith only [h0, h6137, h6782, h6893, h6917, h6919, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6921 | h6921
                        · linarith only [h0, h6137, h6782, h6895, h6917, h6921, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6923 | h6923
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6924 | h6924
                            · linarith only [h6138, h6781, h6782, h6917, h6919, h6924, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6926 | h6926
                              · linarith only [h6137, h6895, h6916, h6926, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6928 | h6928
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6929 | h6929
                                  · rcases h1bigk with h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h0, hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h0, h6916, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6138, hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h0, h6782, h6916, h6917, h6921, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      rcases p6930_3 (m.d 0 1) (by simp) with h6938 | h6938
                                      · linarith only [h0, h6938, hlam]
                                      · linarith only [h6137, h6938, hlam]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6782, h6917, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      rcases p6930_3 (m.d 0 1) (by simp) with h6942 | h6942
                                      · linarith only [h0, h6942, hlam]
                                      · linarith only [h6780, h6942, hlam]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6137, hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6916, hlam, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6919, hlam, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6921, hlam, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6780, h6916, h6921, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6917, hlam, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6916, h6919, hc23, hc34, hlam, hphi, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6916, h6919, h6921, hc23, hc34, hlam, hphi, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6780, hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6918, hlam, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6780, h6916, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6923, hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [hlam, p6930_0]
                                  · linarith only [h6137, h6138, h6916, h6919, h6929, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h0, h6780, h6782, h6923, h6928, hlam]
                          · linarith only [h0, h6780, h6782, h6916, h6917, h6921, h6923, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h6782, h6892, h6918, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6964 | h6964
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6965 | h6965
                      · linarith only [h0, h6137, h6917, h6965, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6967 | h6967
                        · linarith only [h6137, h6895, h6967, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6969 | h6969
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6970 | h6970
                            · linarith only [h0, h6780, h6916, h6917, h6965, h6967, h6970, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h6780, h6916, h6917, h6967, h6970, hc23, hc34, hlam, hphi]
                          · linarith only [h6138, h6780, h6916, h6967, h6969, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6780, h6782, h6892, h6964, hc04, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h6781, h6916, hlam]
              · linarith only [h0, h6780, h6782, h6915, hlam]
        · linarith only [h0, h6780, h6892, hlam]
    · linarith only [h0, h6137, h6781, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6979 | h6979
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6980 | h6980
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6981 | h6981
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6982 | h6982
          · linarith only [h6137, h6138, h6982, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6984 | h6984
            · linarith only [h6137, h6780, h6984, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6986 | h6986
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6987 | h6987
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6988 | h6988
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6989 | h6989
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6990 | h6990
                      · linarith only [h6137, h6138, h6982, h6988, h6990, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6992 | h6992
                        · linarith only [h6137, h6780, h6984, h6992, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6994 | h6994
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6995 | h6995
                            · linarith only [h6137, h6138, h6987, h6990, h6995, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6997 | h6997
                              · linarith only [h6137, h6780, h6979, h6992, h6997, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6999 | h6999
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7000 | h7000
                                  · rcases h1bigk with h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c | h7001c
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [hlam, p7001_0]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h0, hlam, p7001_0]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h6780, h6987, h6994, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7001_1]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h6138, hlam, p7001_0]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h6780, hlam, p7001_0]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p7001_1]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [hlam, p7001_0]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      rcases p7001_3 (m.d 0 1) (by simp) with h7009 | h7009
                                      · linarith only [h0, h7009, hlam]
                                      · linarith only [h6137, h7009, hlam]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h6137, h6138, h6987, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7001_1]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h6137, h6780, h6987, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7001_1]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h6137, hlam, p7001_0]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h6987, hlam, p7001_1]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [hlam, p7001_0]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h6990, hlam, p7001_1]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h6992, hlam, p7001_1]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h6137, h6987, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7001_1]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h6988, hlam, p7001_1]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h6987, h6990, hc23, hc34, hlam, hphi, p7001_1]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [hlam, p7001_0]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h6137, h6780, h6987, h6990, hc23, hc34, hlam, hphi, p7001_1]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h6137, h6987, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7001_1]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h6989, hlam, p7001_1]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h6987, h6992, hc23, hc35, hlam, hphi, p7001_1]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [h6994, hlam, p7001_0]
                                    · have p7001_0 := h7001c.1
                                      have p7001_1 := h7001c.2.1
                                      have p7001_2 := h7001c.2.2.1
                                      have p7001_3 := h7001c.2.2.2
                                      linarith only [hlam, p7001_0]
                                  · linarith only [h6137, h6138, h6987, h6990, h7000, hc23, hc45, hlam, hphi, ht34]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7030 | h7030
                                  · rcases h1bigk with h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c | h7031c
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [hlam, p7031_0]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h0, hlam, p7031_0]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h6780, h6987, h6994, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7031_1]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h6138, hlam, p7031_0]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h6780, hlam, p7031_0]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p7031_1]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [hlam, p7031_0]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      rcases p7031_3 (m.d 0 1) (by simp) with h7039 | h7039
                                      · linarith only [h0, h7039, hlam]
                                      · linarith only [h6137, h7039, hlam]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h6137, h6138, h6987, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7031_1]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h6137, h6780, h6987, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7031_1]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h6137, hlam, p7031_0]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h6987, hlam, p7031_1]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [hlam, p7031_0]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h6990, hlam, p7031_1]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h6992, hlam, p7031_1]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h6137, h6987, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7031_1]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h6988, hlam, p7031_1]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h6987, h6990, hc23, hc34, hlam, hphi, p7031_1]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [hlam, p7031_0]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h6137, h6780, h6987, h6990, hc23, hc34, hlam, hphi, p7031_1]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h6137, h6987, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7031_1]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h6989, hlam, p7031_1]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h6987, h6992, h7030, hc23, hc34, hlam, hphi, p7031_1]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [h6994, hlam, p7031_0]
                                    · have p7031_0 := h7031c.1
                                      have p7031_1 := h7031c.2.1
                                      have p7031_2 := h7031c.2.2.1
                                      have p7031_3 := h7031c.2.2.2
                                      linarith only [hlam, p7031_0]
                                  · linarith only [h6137, h6138, h6986, h6987, h6990, h7030, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · linarith only [h6137, h6138, h6987, h6994, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6980, h6981, h6986, h6989, hlam]
                  · linarith only [h0, h6980, h6988, hlam]
                · linarith only [h0, h6979, h6987, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7064 | h7064
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7065 | h7065
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7066 | h7066
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7067 | h7067
                      · linarith only [h6137, h6138, h6982, h7067, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7069 | h7069
                        · linarith only [h6137, h6984, h7069, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7071 | h7071
                          · linarith only [h6137, h6138, h6986, h7064, h7067, h7071, hc23, hc34, hlam, hphi]
                          · linarith only [h6137, h6138, h7064, h7071, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6981, h7066, hlam]
                  · linarith only [h0, h6980, h7065, hlam]
                · linarith only [h0, h6979, h7064, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7077 | h7077
          · linarith only [h6137, h6138, h7077, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7079 | h7079
            · linarith only [h0, h6137, h6981, h7079, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7081 | h7081
              · linarith only [h6980, h6981, h7081, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7083 | h7083
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7084 | h7084
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7085 | h7085
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7086 | h7086
                      · linarith only [h6137, h6138, h6980, h6981, h7077, h7085, h7086, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7088 | h7088
                        · linarith only [h6137, h6138, h6980, h6981, h7079, h7088, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7090 | h7090
                          · linarith only [h6137, h6138, h7081, h7086, h7090, hc13, hc34, hlam, hphi]
                          · linarith only [h6137, h6138, h7083, h7090, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7093 | h7093
                      · linarith only [h0, h6137, h7085, h7093, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7095 | h7095
                        · linarith only [h6137, h6138, h7084, h7085, h7095, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7097 | h7097
                          · linarith only [h6137, h6138, h7081, h7083, h7084, h7085, h7097, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · linarith only [h6137, h6138, h7083, h7097, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h6137, h6980, h7083, h7084, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h6979, h7083, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7102 | h7102
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7103 | h7103
          · linarith only [h6137, h6138, h7103, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7105 | h7105
            · linarith only [h6137, h6780, h7105, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7107 | h7107
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7108 | h7108
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7109 | h7109
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7110 | h7110
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7111 | h7111
                      · linarith only [h6137, h6780, h6980, h7102, h7103, h7109, h7111, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7113 | h7113
                        · linarith only [h6137, h6780, h7105, h7113, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7115 | h7115
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7116 | h7116
                            · linarith only [h6780, h6979, h6980, h7109, h7111, h7115, h7116, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7118 | h7118
                              · linarith only [h0, h6137, h6980, h7108, h7109, h7118, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7120 | h7120
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7121 | h7121
                                  · rcases h1bigk with h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c | h7122c
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [hlam, p7122_0]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h0, hlam, p7122_0]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h6780, h6980, h7102, h7108, h7109, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7122_1]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h6138, hlam, p7122_0]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h6780, hlam, p7122_0]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p7122_1]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [hlam, p7122_0]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      rcases p7122_3 (m.d 0 1) (by simp) with h7130 | h7130
                                      · linarith only [h0, h7130, hlam]
                                      · linarith only [h6137, h7130, hlam]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h6980, h7109, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7122_1]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h6137, h6780, h7108, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7122_1]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h6137, hlam, p7122_0]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h7108, hlam, p7122_1]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [hlam, p7122_0]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h7111, hlam, p7122_1]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h7113, hlam, p7122_1]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h6137, h7108, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7122_1]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h7109, hlam, p7122_1]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h7108, h7111, hc23, hc34, hlam, hphi, p7122_1]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [hlam, p7122_0]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h6137, h6780, h7108, h7111, hc23, hc34, hlam, hphi, p7122_1]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h6137, h7108, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7122_1]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h7110, hlam, p7122_1]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h7108, h7113, hc23, hc35, hlam, hphi, p7122_1]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [h7115, hlam, p7122_0]
                                    · have p7122_0 := h7122c.1
                                      have p7122_1 := h7122c.2.1
                                      have p7122_2 := h7122c.2.2.1
                                      have p7122_3 := h7122c.2.2.2
                                      linarith only [hlam, p7122_0]
                                  · linarith only [h6137, h6138, h7108, h7111, h7121, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h6137, h6780, h6980, h7102, h7107, h7108, h7120, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · linarith only [h6137, h6138, h7108, h7115, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h6980, h7109, h7110, hc02, hc25, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7154 | h7154
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7155 | h7155
                      · linarith only [h6137, h6780, h7109, h7154, h7155, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7157 | h7157
                        · linarith only [h6137, h6780, h7109, h7154, h7157, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7159 | h7159
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7160 | h7160
                            · linarith only [h6137, h6780, h7108, h7109, h7154, h7155, h7160, hlam]
                            · linarith only [h6137, h6780, h7109, h7154, h7160, hc13, hc34, hlam, hphi]
                          · linarith only [h6137, h6780, h7107, h7108, h7109, h7154, h7159, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h6137, h7102, h7108, h7154, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h6979, h7108, hlam]
              · linarith only [h6980, h7102, h7107, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7167 | h7167
          · linarith only [h0, h6137, h6980, h7167, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7169 | h7169
            · linarith only [h6137, h6780, h7169, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7171 | h7171
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7172 | h7172
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7173 | h7173
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7174 | h7174
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7175 | h7175
                      · linarith only [h0, h6137, h6980, h7167, h7173, h7175, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7177 | h7177
                        · linarith only [h0, h6137, h7102, h7169, h7177, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7179 | h7179
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7180 | h7180
                            · linarith only [h6979, h7102, h7174, h7175, h7179, h7180, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7182 | h7182
                              · linarith only [h0, h6137, h7102, h7172, h7174, h7177, h7182, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7184 | h7184
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7185 | h7185
                                  · rcases h1bigk with h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c | h7186c
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [hlam, p7186_0]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h0, hlam, p7186_0]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h0, h7102, h7173, h7184, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7186_1]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h6138, hlam, p7186_0]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h6780, hlam, p7186_0]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p7186_1]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [hlam, p7186_0]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      rcases p7186_3 (m.d 0 1) (by simp) with h7194 | h7194
                                      · linarith only [h0, h7194, hlam]
                                      · linarith only [h6137, h7194, hlam]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h7102, h7174, h7179, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7186_1]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h0, h6137, h7102, h7172, h7174, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7186_1]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h6137, hlam, p7186_0]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h7172, hlam, p7186_1]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [hlam, p7186_0]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h7175, hlam, p7186_1]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h7177, hlam, p7186_1]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h6137, h7172, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7186_1]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h7173, hlam, p7186_1]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h7172, h7175, hc23, hc34, hlam, hphi, p7186_1]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [hlam, p7186_0]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h0, h6137, h7102, h7172, h7174, h7175, hc23, hc34, hlam, hphi, p7186_1]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h6137, h7172, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7186_1]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h7174, hlam, p7186_1]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h7172, h7177, hc23, hc35, hlam, hphi, p7186_1]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [h7179, hlam, p7186_0]
                                    · have p7186_0 := h7186c.1
                                      have p7186_1 := h7186c.2.1
                                      have p7186_2 := h7186c.2.2.1
                                      have p7186_3 := h7186c.2.2.2
                                      linarith only [hlam, p7186_0]
                                  · linarith only [h6137, h6138, h7172, h7175, h7185, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h0, h6137, h6980, h7171, h7172, h7184, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · linarith only [h6137, h6138, h7172, h7179, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6137, h6980, h7172, h7173, h7174, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7218 | h7218
                    · linarith only [h0, h6137, h7102, h7172, h7173, h7218, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7220 | h7220
                      · linarith only [h0, h6137, h7173, h7220, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7222 | h7222
                        · linarith only [h0, h6137, h7173, h7222, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7224 | h7224
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7225 | h7225
                            · linarith only [h0, h6137, h7172, h7173, h7220, h7225, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h6137, h7172, h7173, h7225, hc23, hc34, hlam, hphi]
                          · linarith only [h6137, h6138, h7172, h7224, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h6137, h6979, h7172, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7230 | h7230
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7231 | h7231
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7232 | h7232
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7233 | h7233
                      · linarith only [h0, h6137, h6980, h7231, h7233, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7235 | h7235
                        · linarith only [h0, h6137, h6980, h7231, h7235, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7237 | h7237
                          · linarith only [h6137, h6138, h7171, h7233, h7237, hc13, hc34, hlam, hphi]
                          · linarith only [h6137, h6138, h7230, h7237, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6137, h6980, h7230, h7231, h7232, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7241 | h7241
                    · linarith only [h0, h6137, h7102, h7230, h7231, h7241, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7243 | h7243
                      · linarith only [h0, h6137, h7231, h7243, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7245 | h7245
                        · linarith only [h0, h6137, h7231, h7245, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7247 | h7247
                          · linarith only [h0, h6137, h6980, h7171, h7230, h7243, h7247, hc23, hc34, hlam, hphi]
                          · linarith only [h6137, h6138, h7230, h7247, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h6137, h6979, h6980, h7230, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · linarith only [h0, h6137, h6979, hlam]

set_option maxHeartbeats 10428000 in
set_option maxHeartbeats 10428000 in
theorem r1l7_21_15_H_I_L_I_s7_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6137 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h6138 | h6138
  · exact r1l7_21_15_H_I_L_I_s7_x0_x0 m hb1 hb5 hg0 h6137 h6138
  · exact r1l7_21_15_H_I_L_I_s7_x0_x1 m hb1 hb5 hg0 h6137 h6138

set_option maxHeartbeats 10428000 in
set_option maxHeartbeats 10428000 in
theorem r1l7_21_15_H_I_L_I_s7_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6137 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0 := hg0
  exact r1l7_21_15_H_I_L_I_s8 m hb1 hb5 h0 h6137

set_option maxHeartbeats 10428000 in
set_option maxHeartbeats 10428000 in
theorem r1l7_21_15_H_I_L_I_s7 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h6137 | h6137
  · exact r1l7_21_15_H_I_L_I_s7_x0 m hb1 hb5 hg0 h6137
  · exact r1l7_21_15_H_I_L_I_s7_x1 m hb1 hb5 hg0 h6137

set_option maxHeartbeats 22702000 in
set_option maxHeartbeats 22702000 in
theorem r1l7_21_15_H_I_L_I (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_21_15_H_I_L_I_s0 m hb1 hb5 h0
  · exact r1l7_21_15_H_I_L_I_s7 m hb1 hb5 h0

end R2N4
