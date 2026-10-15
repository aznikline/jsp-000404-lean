import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_19S8
import Jsp000404.R1LeavesN7_19S13
import Jsp000404.R1LeavesN7_19S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7184000 in
set_option maxHeartbeats 7184000 in
theorem r1l7_21_14_H_I_L_I_s5_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5235 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h5236 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h5759 | h5759
  · rcases m.htr 0 2 4 (by decide) (by decide) with h5760 | h5760
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5761 | h5761
      · linarith only [h5235, h5236, h5761, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5763 | h5763
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5764 | h5764
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5765 | h5765
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5766 | h5766
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5767 | h5767
                · linarith only [h5235, h5236, h5761, h5765, h5767, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5769 | h5769
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5770 | h5770
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5771 | h5771
                      · linarith only [h5235, h5236, h5767, h5769, h5771, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5773 | h5773
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5774 | h5774
                          · rcases h1bigk with h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c | h5775c
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [hlam, p5775_0]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [h0, hlam, p5775_0]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [h5769, h5774, hc01, hc45, hlam, hphi, ht0b, ht5b, p5775_1]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [h5236, hlam, p5775_0]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [h5236, h5767, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5775_1]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p5775_1]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [hlam, p5775_0]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [h5769, h5774, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5775_1]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [h5235, h5236, h5769, h5774, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5775_1]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              rcases p5775_3 (m.d 0 1) (by simp) with h5785 | h5785
                              · linarith only [h0, h5785, hlam]
                              · linarith only [h5759, h5785, hlam]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [h5235, hlam, p5775_0]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [h5764, hlam, p5775_0]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [hlam, p5775_0]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [h5767, hlam, p5775_0]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [h5235, h5769, h5774, hc01, hc45, hlam, hphi, ht0b, ht5b, p5775_1]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p5775_1]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [h5765, hlam, p5775_0]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [h5764, h5767, hc23, hc34, hlam, hphi, p5775_1]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [hlam, p5775_0]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              rcases p5775_3 (m.d 0 1) (by simp) with h5797 | h5797
                              · linarith only [h5236, h5797, hlam]
                              · linarith only [h5759, h5797, hlam]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [h5759, hlam, p5775_0]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [h5766, hlam, p5775_0]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [h5769, hlam, p5775_0]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [h5770, hlam, p5775_0]
                            · have p5775_0 := h5775c.1
                              have p5775_1 := h5775c.2.1
                              have p5775_2 := h5775c.2.2.1
                              have p5775_3 := h5775c.2.2.2
                              linarith only [hlam, p5775_0]
                          · linarith only [h5235, h5236, h5767, h5769, h5774, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h5235, h5236, h5767, h5769, h5770, h5771, h5773, hc23, hc34, hlam, hphi]
                    · linarith only [h5235, h5236, h5770, hc13, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5808 | h5808
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5809 | h5809
                      · linarith only [h5236, h5759, h5764, h5767, h5769, h5809, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5811 | h5811
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5812 | h5812
                          · rcases h1bigk with h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c | h5813c
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [hlam, p5813_0]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [h0, hlam, p5813_0]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [h5236, h5764, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5813_1]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [h5236, hlam, p5813_0]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [h5236, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p5813_1]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p5813_1]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [hlam, p5813_0]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              rcases p5813_3 (m.d 0 1) (by simp) with h5821 | h5821
                              · linarith only [h0, h5821, hlam]
                              · linarith only [h5235, h5821, hlam]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [h5236, h5759, h5764, h5769, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5813_1]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              rcases p5813_3 (m.d 0 1) (by simp) with h5825 | h5825
                              · linarith only [h0, h5825, hlam]
                              · linarith only [h5759, h5825, hlam]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [h5235, hlam, p5813_0]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [h5764, hlam, p5813_0]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [hlam, p5813_0]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [h5767, hlam, p5813_0]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [h5769, hlam, p5813_1]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [h5759, h5764, h5769, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5813_1]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [h5765, hlam, p5813_0]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [h5764, h5767, hc23, hc34, hlam, hphi, p5813_1]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [hlam, p5813_0]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [h5764, h5767, h5769, hc23, hc34, hlam, hphi, p5813_1]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [h5759, hlam, p5813_0]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [h5766, hlam, p5813_0]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [h5759, h5764, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5813_1]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [h5808, hlam, p5813_0]
                            · have p5813_0 := h5813c.1
                              have p5813_1 := h5813c.2.1
                              have p5813_2 := h5813c.2.2.1
                              have p5813_3 := h5813c.2.2.2
                              linarith only [hlam, p5813_0]
                          · linarith only [h5236, h5767, h5811, h5812, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h5236, h5759, h5767, h5808, h5809, h5811, hc23, hc34, hlam, hphi]
                    · linarith only [h5235, h5236, h5764, h5808, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h5759, h5766, hlam]
            · linarith only [h0, h5760, h5765, hlam]
          · linarith only [h0, h5235, h5764, hlam]
        · linarith only [h5236, h5759, h5763, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5850 | h5850
      · linarith only [h0, h5235, h5760, h5850, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5852 | h5852
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5853 | h5853
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5854 | h5854
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5855 | h5855
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5856 | h5856
                · linarith only [h0, h5235, h5760, h5850, h5854, h5856, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5858 | h5858
                  · linarith only [h0, h5235, h5760, h5854, h5858, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5860 | h5860
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5861 | h5861
                      · linarith only [h0, h5760, h5853, h5854, h5856, h5861, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5863 | h5863
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5864 | h5864
                          · rcases h1bigk with h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [hlam, p5865_0]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [h0, hlam, p5865_0]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [h0, h5760, h5853, h5854, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5865_1]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [h5236, hlam, p5865_0]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [h0, h5760, h5853, h5854, h5856, h5858, hc23, hc34, hlam, hphi, p5865_1]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p5865_1]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [hlam, p5865_0]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              rcases p5865_3 (m.d 0 1) (by simp) with h5873 | h5873
                              · linarith only [h0, h5873, hlam]
                              · linarith only [h5235, h5873, hlam]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [h5236, h5759, h5853, h5858, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5865_1]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              rcases p5865_3 (m.d 0 1) (by simp) with h5877 | h5877
                              · linarith only [h0, h5877, hlam]
                              · linarith only [h5759, h5877, hlam]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [h5235, hlam, p5865_0]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [h5853, hlam, p5865_0]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [hlam, p5865_0]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [h5856, hlam, p5865_0]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [h5858, hlam, p5865_1]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [h5759, h5853, h5858, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5865_1]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [h5854, hlam, p5865_0]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [h5853, h5856, hc23, hc34, hlam, hphi, p5865_1]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [hlam, p5865_0]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [h5853, h5856, h5858, hc23, hc34, hlam, hphi, p5865_1]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [h5759, hlam, p5865_0]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [h5855, hlam, p5865_0]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [h5759, h5853, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5865_1]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [h5860, hlam, p5865_0]
                            · have p5865_0 := h5865c.1
                              have p5865_1 := h5865c.2.1
                              have p5865_2 := h5865c.2.2.1
                              have p5865_3 := h5865c.2.2.2
                              linarith only [hlam, p5865_0]
                          · linarith only [h0, h5759, h5760, h5854, h5855, h5856, h5863, h5864, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h5235, h5760, h5853, h5863, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h5759, h5760, h5852, h5854, h5860, hc04, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h5235, h5760, h5853, h5854, h5855, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5899 | h5899
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5900 | h5900
                · linarith only [h0, h5235, h5850, h5854, h5900, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5902 | h5902
                  · linarith only [h0, h5235, h5854, h5902, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5904 | h5904
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5905 | h5905
                      · linarith only [h0, h5759, h5853, h5854, h5900, h5902, h5905, hlam]
                      · linarith only [h0, h5759, h5853, h5854, h5902, h5905, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h5759, h5853, h5854, h5902, h5904, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h5759, h5899, hlam]
          · linarith only [h0, h5235, h5853, hlam]
        · linarith only [h0, h5759, h5760, h5852, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h5912 | h5912
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5913 | h5913
      · linarith only [h5235, h5236, h5913, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5915 | h5915
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5916 | h5916
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5917 | h5917
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5918 | h5918
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5919 | h5919
                · linarith only [h5235, h5236, h5913, h5917, h5919, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5921 | h5921
                  · linarith only [h5235, h5759, h5921, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5923 | h5923
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5924 | h5924
                      · linarith only [h5759, h5916, h5919, h5923, h5924, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5926 | h5926
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5927 | h5927
                          · rcases h1bigk with h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c | h5928c
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [hlam, p5928_0]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h0, hlam, p5928_0]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h5759, h5916, h5923, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5928_1]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h5236, hlam, p5928_0]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h5759, hlam, p5928_0]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p5928_1]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [hlam, p5928_0]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              rcases p5928_3 (m.d 0 1) (by simp) with h5936 | h5936
                              · linarith only [h0, h5936, hlam]
                              · linarith only [h5235, h5936, hlam]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h5235, h5236, h5916, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5928_1]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h5235, h5759, h5916, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5928_1]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h5235, hlam, p5928_0]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h5916, hlam, p5928_0]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [hlam, p5928_0]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h5919, hlam, p5928_0]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h5921, hlam, p5928_1]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h5235, h5916, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5928_1]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h5917, hlam, p5928_0]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h5916, h5919, hc23, hc34, hlam, hphi, p5928_1]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [hlam, p5928_0]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h5235, h5759, h5916, h5919, hc23, hc34, hlam, hphi, p5928_1]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h5235, h5916, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5928_1]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h5918, hlam, p5928_0]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h5916, h5921, hc23, hc35, hlam, hphi, p5928_1]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [h5923, hlam, p5928_0]
                            · have p5928_0 := h5928c.1
                              have p5928_1 := h5928c.2.1
                              have p5928_2 := h5928c.2.2.1
                              have p5928_3 := h5928c.2.2.2
                              linarith only [hlam, p5928_0]
                          · linarith only [h0, h5235, h5236, h5912, h5916, h5919, h5926, h5927, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5957 | h5957
                          · rcases h1bigk with h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c | h5958c
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [hlam, p5958_0]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h0, hlam, p5958_0]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h5759, h5916, h5923, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5958_1]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h5236, hlam, p5958_0]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h5759, hlam, p5958_0]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p5958_1]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [hlam, p5958_0]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              rcases p5958_3 (m.d 0 1) (by simp) with h5966 | h5966
                              · linarith only [h0, h5966, hlam]
                              · linarith only [h5235, h5966, hlam]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h5235, h5236, h5916, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5958_1]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h5235, h5759, h5916, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5958_1]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h5235, hlam, p5958_0]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h5916, hlam, p5958_0]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [hlam, p5958_0]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h5919, hlam, p5958_0]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h5921, hlam, p5958_1]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h5235, h5916, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5958_1]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h5917, hlam, p5958_0]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h5916, h5919, hc23, hc34, hlam, hphi, p5958_1]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [hlam, p5958_0]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h5235, h5759, h5916, h5919, hc23, hc34, hlam, hphi, p5958_1]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h5235, h5916, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5958_1]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h5918, hlam, p5958_0]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h5916, h5921, h5957, hc23, hc34, hlam, hphi, p5958_1]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [h5923, hlam, p5958_0]
                            · have p5958_0 := h5958c.1
                              have p5958_1 := h5958c.2.1
                              have p5958_2 := h5958c.2.2.1
                              have p5958_3 := h5958c.2.2.2
                              linarith only [hlam, p5958_0]
                          · linarith only [h5235, h5236, h5915, h5916, h5919, h5957, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h5236, h5915, h5923, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5988 | h5988
                · linarith only [h0, h5235, h5918, h5988, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5990 | h5990
                  · linarith only [h5235, h5236, h5917, h5918, h5990, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5992 | h5992
                    · linarith only [h5917, h5918, h5992, hlam]
                    · linarith only [h0, h5236, h5912, h5915, h5918, h5992, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h5912, h5917, hlam]
          · linarith only [h0, h5235, h5916, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5997 | h5997
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5998 | h5998
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5999 | h5999
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6000 | h6000
                · linarith only [h5235, h5236, h5913, h6000, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6002 | h6002
                  · linarith only [h5235, h5759, h6002, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6004 | h6004
                    · linarith only [h5235, h5236, h5915, h6000, h6004, hc13, hc34, hlam, hphi]
                    · linarith only [h5235, h5236, h5997, h6004, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6007 | h6007
                · linarith only [h5235, h5236, h5998, h5999, h6007, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6009 | h6009
                  · linarith only [h5235, h5236, h5998, h5999, h6009, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6011 | h6011
                    · linarith only [h5235, h5236, h5915, h5997, h5998, h5999, h6011, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h5235, h5236, h5997, h6011, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h0, h5912, h5998, hlam]
          · linarith only [h0, h5235, h5997, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6016 | h6016
      · linarith only [h0, h5235, h5912, h6016, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6018 | h6018
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6019 | h6019
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6020 | h6020
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6021 | h6021
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6022 | h6022
                · linarith only [h0, h5235, h5912, h6016, h6020, h6022, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6024 | h6024
                  · linarith only [h0, h5235, h5912, h6020, h6024, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6026 | h6026
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6027 | h6027
                      · linarith only [h0, h5235, h5912, h6019, h6020, h6022, h6027, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6029 | h6029
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6030 | h6030
                          · rcases h1bigk with h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [hlam, p6031_0]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h0, hlam, p6031_0]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h0, h5912, h6019, h6020, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6031_1]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h5236, hlam, p6031_0]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h5759, hlam, p6031_0]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p6031_1]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [hlam, p6031_0]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              rcases p6031_3 (m.d 0 1) (by simp) with h6039 | h6039
                              · linarith only [h0, h6039, hlam]
                              · linarith only [h5235, h6039, hlam]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h5912, h6020, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6031_1]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h5235, h5759, h6019, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6031_1]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h5235, hlam, p6031_0]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h6019, hlam, p6031_0]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [hlam, p6031_0]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h6022, hlam, p6031_0]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h6024, hlam, p6031_1]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h5235, h6019, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6031_1]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h6020, hlam, p6031_0]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h6019, h6022, hc23, hc34, hlam, hphi, p6031_1]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [hlam, p6031_0]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h5235, h5759, h6019, h6022, hc23, hc34, hlam, hphi, p6031_1]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h5235, h6019, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6031_1]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h6021, hlam, p6031_0]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h6019, h6024, h6030, hc23, hc34, hlam, hphi, p6031_1]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [h6026, hlam, p6031_0]
                            · have p6031_0 := h6031c.1
                              have p6031_1 := h6031c.2.1
                              have p6031_2 := h6031c.2.2.1
                              have p6031_3 := h6031c.2.2.2
                              linarith only [hlam, p6031_0]
                          · linarith only [h5235, h5236, h6019, h6022, h6030, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h5235, h5912, h6018, h6019, h6029, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h5912, h6018, h6020, h6026, hlam]
              · linarith only [h0, h5235, h5912, h6019, h6020, h6021, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6063 | h6063
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6064 | h6064
                · linarith only [h5235, h5759, h6016, h6020, h6063, h6064, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6066 | h6066
                  · linarith only [h5235, h5759, h6020, h6063, h6066, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6068 | h6068
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6069 | h6069
                      · linarith only [h5235, h5759, h6019, h6020, h6063, h6064, h6069, hlam]
                      · linarith only [h5235, h5759, h6019, h6020, h6063, h6069, hc23, hc34, hlam, hphi]
                    · linarith only [h5235, h5759, h6018, h6019, h6020, h6063, h6068, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6073 | h6073
                · linarith only [h0, h5235, h6016, h6063, h6073, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6075 | h6075
                  · linarith only [h0, h5235, h6063, h6075, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6077 | h6077
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6078 | h6078
                      · linarith only [h0, h5235, h6019, h6063, h6073, h6078, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h5235, h6019, h6020, h6078, hc23, hc34, hlam, hphi]
                    · linarith only [h5235, h5236, h6018, h6019, h6077, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h0, h5235, h6019, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6083 | h6083
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6084 | h6084
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6085 | h6085
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6086 | h6086
                · linarith only [h0, h5235, h5912, h6084, h6086, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6088 | h6088
                  · linarith only [h0, h5235, h5912, h6084, h6088, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6090 | h6090
                    · linarith only [h5235, h5236, h6018, h6086, h6090, hc13, hc34, hlam, hphi]
                    · linarith only [h5235, h5236, h6083, h6090, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h5912, h6084, h6085, hc02, hc25, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6094 | h6094
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6095 | h6095
                · linarith only [h0, h5235, h6084, h6095, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6097 | h6097
                  · linarith only [h5235, h5759, h6084, h6094, h6097, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6099 | h6099
                    · linarith only [h5235, h5236, h6018, h6095, h6099, hc13, hc34, hlam, hphi]
                    · linarith only [h5235, h5236, h6083, h6099, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6102 | h6102
                · linarith only [h0, h5235, h6084, h6102, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6104 | h6104
                  · linarith only [h0, h5235, h6084, h6104, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6106 | h6106
                    · linarith only [h0, h5235, h5912, h6018, h6083, h6102, h6106, hc23, hc34, hlam, hphi]
                    · linarith only [h5235, h5236, h6083, h6106, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h0, h5235, h6083, hlam]

set_option maxHeartbeats 7184000 in
set_option maxHeartbeats 7184000 in
theorem r1l7_21_14_H_I_L_I_s5_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5235 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h5236 | h5236
  · exact r1l7_21_14_H_I_L_I_s5_x0_x0 m hb1 hb4 hg0 h5235 h5236
  · exact r1l7_21_14_H_I_L_I_s5_x0_x1 m hb1 hb4 hg0 h5235 h5236

set_option maxHeartbeats 7184000 in
set_option maxHeartbeats 7184000 in
theorem r1l7_21_14_H_I_L_I_s5_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5235 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  exact r1l7_21_14_H_I_L_I_s6 m hb1 hb4 h0 h5235

set_option maxHeartbeats 7184000 in
set_option maxHeartbeats 7184000 in
theorem r1l7_21_14_H_I_L_I_s5 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h5235 | h5235
  · exact r1l7_21_14_H_I_L_I_s5_x0 m hb1 hb4 hg0 h5235
  · exact r1l7_21_14_H_I_L_I_s5_x1 m hb1 hb4 hg0 h5235

set_option maxHeartbeats 17654000 in
set_option maxHeartbeats 17654000 in
theorem r1l7_21_14_H_I_L_I (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4bigk := hb4.1
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_21_14_H_I_L_I_s0 m hb1 hb4 h0
  · exact r1l7_21_14_H_I_L_I_s5 m hb1 hb4 h0

end R2N4
