import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_13S12
import Jsp000404.R1LeavesN7_13S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7524000 in
set_option maxHeartbeats 7524000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s8_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7870 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8661 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h11104 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h11557 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  have h6923 := hg6923
  have h7870 := hg7870
  rcases m.htr 0 3 4 (by decide) (by decide) with h11794 | h11794
  · rcases m.htr 0 3 5 (by decide) (by decide) with h11795 | h11795
    · rcases m.htr 0 4 5 (by decide) (by decide) with h11796 | h11796
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11797 | h11797
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11798 | h11798
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11799 | h11799
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11800 | h11800
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11801 | h11801
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11802 | h11802
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11803 | h11803
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11804 | h11804
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11805 | h11805
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11806 | h11806
                          · rcases h2bigk with h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [hlam, p11807_0]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h0, hlam, p11807_0]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h8661, hlam, p11807_0]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h11104, hlam, p11807_0]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h11557, hlam, p11807_0]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p11807_1]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [hlam, p11807_0]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h0, h8661, hc01, hc12, hlam, hphi, p11807_1]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h0, h11104, hc01, hc12, hlam, hphi, p11807_1]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h0, h11557, hc01, hc12, hlam, hphi, p11807_1]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h0, h11797, hc01, hc13, hlam, hphi, p11807_1]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h11797, hlam, p11807_0]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [hlam, p11807_0]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h0, h11557, h11797, h11805, hc01, hc12, hlam, hphi, p11807_1]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h0, h11557, h11797, hc01, hc12, hlam, hphi, p11807_1]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h0, h11798, hc01, hc14, hlam, hphi, p11807_1]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h11798, hlam, p11807_0]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h11803, hlam, p11807_0]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [hlam, p11807_0]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h0, h11557, h11797, h11803, hc01, hc12, hlam, hphi, p11807_1]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h0, h11799, hc01, hc15, hlam, hphi, p11807_1]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h11799, hlam, p11807_0]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h11804, hlam, p11807_0]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [h11805, hlam, p11807_1]
                            · have p11807_0 := h11807c.1
                              have p11807_1 := h11807c.2.1
                              have p11807_2 := h11807c.2.2.1
                              have p11807_3 := h11807c.2.2.2
                              linarith only [hlam, p11807_0]
                          · rcases h2bigk with h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c | h11833c
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [hlam, p11833_0]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h0, hlam, p11833_0]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h8661, hlam, p11833_0]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h11104, hlam, p11833_0]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h11557, hlam, p11833_0]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p11833_1]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [hlam, p11833_0]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h11104, h11796, h11803, h11806, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p11833_1]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h0, h11557, h11805, hc01, hc12, hlam, hphi, p11833_1]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h0, h11557, hc01, hc12, hlam, hphi, p11833_1]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p11833_1]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h11797, hlam, p11833_0]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [hlam, p11833_0]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h0, h11557, h11797, h11805, hc01, hc12, hlam, hphi, p11833_1]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h0, h11557, h11797, hc01, hc12, hlam, hphi, p11833_1]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p11833_1]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h11798, hlam, p11833_0]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h11803, hlam, p11833_0]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [hlam, p11833_0]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h0, h11557, h11797, h11803, hc01, hc12, hlam, hphi, p11833_1]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p11833_1]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h11799, hlam, p11833_0]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h11804, hlam, p11833_0]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [h11805, hlam, p11833_1]
                            · have p11833_0 := h11833c.1
                              have p11833_1 := h11833c.2.1
                              have p11833_2 := h11833c.2.2.1
                              have p11833_3 := h11833c.2.2.2
                              linarith only [hlam, p11833_0]
                        · linarith only [h0, h11104, h11796, h11797, h11800, h11805, h6923, hc01, hc12, hlam, hphi]
                      · linarith only [h11795, h11804, h8661, hlam]
                    · linarith only [h11794, h11803, h8661, hlam]
                  · linarith only [h11796, h11802, h6923, hlam]
                · linarith only [h11794, h11795, h11796, h11801, h5135, hlam]
              · linarith only [h11794, h11797, h11800, h8661, hlam]
            · linarith only [h0, h11797, h11799, h8661, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h11797, h11798, h8661, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11867 | h11867
          · linarith only [h0, h11104, h11797, h11867, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11869 | h11869
            · linarith only [h0, h11557, h11797, h11869, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11871 | h11871
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11872 | h11872
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11873 | h11873
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11874 | h11874
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11875 | h11875
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11876 | h11876
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11877 | h11877
                          · rcases h2bigk with h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c | h11878c
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [hlam, p11878_0]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h0, hlam, p11878_0]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h8661, hlam, p11878_0]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h11104, hlam, p11878_0]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h11557, hlam, p11878_0]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h0, h11869, h11874, h11876, hc01, hc23, hlam, hphi, ht12, p11878_1]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [hlam, p11878_0]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h11797, hlam, p11878_0]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h11867, hlam, p11878_0]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h11869, hlam, p11878_0]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p11878_1]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p11878_1]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [hlam, p11878_0]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h0, h11104, hc01, hc23, hlam, hphi, ht12, p11878_1]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h0, h11869, hc01, hc23, hlam, hphi, ht12, p11878_1]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p11878_1]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p11878_1]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h11874, hlam, p11878_0]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [hlam, p11878_0]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h0, h11869, h11874, hc01, hc23, hlam, hphi, ht12, p11878_1]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p11878_1]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p11878_1]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h11875, hlam, p11878_0]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [h11876, hlam, p11878_1]
                            · have p11878_0 := h11878c.1
                              have p11878_1 := h11878c.2.1
                              have p11878_2 := h11878c.2.2.1
                              have p11878_3 := h11878c.2.2.2
                              linarith only [hlam, p11878_0]
                          · rcases h2bigk with h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c | h11904c
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [hlam, p11904_0]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h0, hlam, p11904_0]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h8661, hlam, p11904_0]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h11104, hlam, p11904_0]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h11557, hlam, p11904_0]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p11904_1]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [hlam, p11904_0]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h11797, hlam, p11904_0]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h11867, hlam, p11904_0]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h11869, hlam, p11904_0]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p11904_1]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p11904_1]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [hlam, p11904_0]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h0, h11104, hc01, hc23, hlam, hphi, ht12, p11904_1]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h0, h11557, hc01, hc23, hlam, hphi, ht12, p11904_1]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p11904_1]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p11904_1]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h11874, hlam, p11904_0]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [hlam, p11904_0]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h0, h11869, h11874, hc01, hc23, hlam, hphi, ht12, p11904_1]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p11904_1]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p11904_1]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h11875, hlam, p11904_0]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [h11876, hlam, p11904_1]
                            · have p11904_0 := h11904c.1
                              have p11904_1 := h11904c.2.1
                              have p11904_2 := h11904c.2.2.1
                              have p11904_3 := h11904c.2.2.2
                              linarith only [hlam, p11904_0]
                        · linarith only [h0, h11104, h11796, h11871, h11876, h6923, hc01, hc13, hlam, hphi]
                      · linarith only [h11795, h11797, h11875, h5135, hlam]
                    · linarith only [h11794, h11797, h11874, h5135, hlam]
                  · linarith only [h11796, h11873, h6923, hlam]
                · linarith only [h11795, h11872, h5135, hlam]
              · linarith only [h11794, h11871, h5135, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11936 | h11936
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11937 | h11937
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11938 | h11938
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11939 | h11939
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11940 | h11940
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11941 | h11941
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11942 | h11942
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11943 | h11943
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11944 | h11944
                        · linarith only [h0, h11104, h11796, h11936, h11942, h11944, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h11104, h11939, h11941, h11944, hc01, hc13, hlam, hphi]
                      · linarith only [h11795, h11943, h8661, hlam]
                    · linarith only [h11794, h11942, h8661, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11949 | h11949
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11950 | h11950
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11951 | h11951
                        · linarith only [h11941, h11951, h6923, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11953 | h11953
                          · linarith only [h11794, h11941, h11953, h6923, h8661, hc01, hc23, hlam, hphi, ht12]
                          · rcases h2bigk with h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c | h11955c
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [hlam, p11955_0]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h0, hlam, p11955_0]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h8661, hlam, p11955_0]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h11104, hlam, p11955_0]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h11557, hlam, p11955_0]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p11955_1]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [hlam, p11955_0]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h11795, h11953, h8661, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11955_1]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h0, h11104, hc01, hc12, hlam, hphi, p11955_1]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h0, h11557, hc01, hc12, hlam, hphi, p11955_1]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p11955_1]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h11936, hlam, p11955_0]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [hlam, p11955_0]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h0, h11104, h11936, hc01, hc12, hlam, hphi, p11955_1]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h0, h11557, h11936, hc01, hc12, hlam, hphi, p11955_1]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p11955_1]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h11937, hlam, p11955_0]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h11949, hlam, p11955_0]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [hlam, p11955_0]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h11951, hlam, p11955_0]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p11955_1]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h11938, hlam, p11955_0]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h11950, hlam, p11955_0]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [h11936, h11950, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11955_1]
                            · have p11955_0 := h11955c.1
                              have p11955_1 := h11955c.2.1
                              have p11955_2 := h11955c.2.2.1
                              have p11955_3 := h11955c.2.2.2
                              linarith only [hlam, p11955_0]
                      · linarith only [h0, h11795, h11936, h11950, h5135, h8661, hc01, hc12, hlam, hphi]
                    · linarith only [h11794, h11949, h8661, hlam]
                · linarith only [h11795, h11940, h5135, h8661, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h11794, h11936, h11939, h8661, hlam]
            · linarith only [h0, h11936, h11938, h8661, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h11936, h11937, h8661, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11987 | h11987
          · linarith only [h0, h11104, h11936, h11987, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11989 | h11989
            · linarith only [h0, h11557, h11936, h11989, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11991 | h11991
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11992 | h11992
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11993 | h11993
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11994 | h11994
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11995 | h11995
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11996 | h11996
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11997 | h11997
                          · linarith only [h0, h11104, h11794, h11796, h11997, h5135, hc01, hc13, hlam, hphi]
                          · rcases h2bigk with h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c | h11999c
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [hlam, p11999_0]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h0, hlam, p11999_0]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h8661, hlam, p11999_0]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h11104, hlam, p11999_0]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h11557, hlam, p11999_0]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p11999_1]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [hlam, p11999_0]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h11936, hlam, p11999_0]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h11987, hlam, p11999_0]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h11989, hlam, p11999_0]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p11999_1]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p11999_1]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [hlam, p11999_0]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h11796, h11987, h11993, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p11999_1]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h0, h11557, hc01, hc23, hlam, hphi, ht12, p11999_1]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p11999_1]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p11999_1]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h11994, hlam, p11999_0]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [hlam, p11999_0]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h11989, h11994, h7870, hc01, hc23, hlam, hphi, ht12, p11999_1]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p11999_1]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p11999_1]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h11995, hlam, p11999_0]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [h11996, hlam, p11999_1]
                            · have p11999_0 := h11999c.1
                              have p11999_1 := h11999c.2.1
                              have p11999_2 := h11999c.2.2.1
                              have p11999_3 := h11999c.2.2.2
                              linarith only [hlam, p11999_0]
                        · linarith only [h0, h11104, h11993, h11996, hc01, hc14, hlam, hphi]
                      · linarith only [h11795, h11936, h11995, h5135, hlam]
                    · linarith only [h11794, h11796, h11936, h11991, h11993, h11994, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12028 | h12028
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12029 | h12029
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12030 | h12030
                        · linarith only [h11993, h12028, h12030, h6923, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h11987, h12030, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h11795, h12029, h5135, h8661, hc01, hc13, hlam, hphi]
                    · linarith only [h11794, h11936, h11993, h12028, h5135, h6923, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h11795, h11992, h5135, hlam]
              · linarith only [h11794, h11991, h5135, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h12037 | h12037
      · linarith only [h11794, h11795, h12037, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h12039 | h12039
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12040 | h12040
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12041 | h12041
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12042 | h12042
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12043 | h12043
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12044 | h12044
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12045 | h12045
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12046 | h12046
                      · linarith only [h11794, h11795, h12039, h12046, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h12043, h12046, h8661, hc01, hc13, hlam, hphi]
                    · linarith only [h0, h11794, h12039, h12045, h5135, h8661, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12050 | h12050
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12051 | h12051
                      · linarith only [h11794, h11795, h12039, h12051, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h12039, h12043, h12051, h8661, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h11794, h12039, h12050, h5135, h8661, hc01, hc12, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12055 | h12055
                  · linarith only [h0, h11104, h12037, h12042, h12043, h12055, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12057 | h12057
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12058 | h12058
                      · linarith only [h12039, h12043, h12058, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12060 | h12060
                        · linarith only [h0, h11104, h12037, h12040, h12060, hc01, hc12, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12062 | h12062
                          · linarith only [h11794, h12043, h12055, h12062, h5135, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases h2bigk with h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c | h12064c
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [hlam, p12064_0]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h0, hlam, p12064_0]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h8661, hlam, p12064_0]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h11104, hlam, p12064_0]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h11557, hlam, p12064_0]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p12064_1]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [hlam, p12064_0]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h11794, h8661, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12064_1]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h0, h11104, hc01, hc12, hlam, hphi, p12064_1]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h11557, h11794, h11795, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12064_1]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h0, h12039, h12043, h12062, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12064_1]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h12039, hlam, p12064_0]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [hlam, p12064_0]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h12039, h12043, h12062, hc24, hc45, hlam, hphi, p12064_1]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h12058, hlam, p12064_1]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p12064_1]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h12040, hlam, p12064_0]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h12057, hlam, p12064_0]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [hlam, p12064_0]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h12060, hlam, p12064_0]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p12064_1]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h12041, hlam, p12064_0]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h0, h12041, h8661, hc01, hc15, hlam, hphi, p12064_1]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [h0, h11104, h12041, hc01, hc12, hlam, hphi, p12064_1]
                            · have p12064_0 := h12064c.1
                              have p12064_1 := h12064c.2.1
                              have p12064_2 := h12064c.2.2.1
                              have p12064_3 := h12064c.2.2.2
                              linarith only [hlam, p12064_0]
                    · linarith only [h11794, h12043, h12057, h5135, hc23, hc35, hlam, hphi]
              · linarith only [h11794, h12042, h5135, hlam]
            · linarith only [h0, h12039, h12041, h8661, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h12039, h12040, h8661, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12094 | h12094
          · linarith only [h0, h11104, h12039, h12094, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12096 | h12096
            · linarith only [h0, h11557, h12039, h12096, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12098 | h12098
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12099 | h12099
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12100 | h12100
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12101 | h12101
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12102 | h12102
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12103 | h12103
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12104 | h12104
                          · linarith only [h0, h11104, h11794, h11795, h12037, h12039, h12099, h12104, hc01, hc23, hlam, hphi, ht12]
                          · rcases h2bigk with h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c | h12106c
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [hlam, p12106_0]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h0, hlam, p12106_0]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h8661, hlam, p12106_0]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h11104, hlam, p12106_0]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h11557, hlam, p12106_0]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h0, h12096, h12101, h12103, hc01, hc23, hlam, hphi, ht12, p12106_1]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [hlam, p12106_0]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h12039, hlam, p12106_0]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h12094, hlam, p12106_0]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h12096, hlam, p12106_0]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p12106_1]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p12106_1]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [hlam, p12106_0]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h0, h11104, hc01, hc23, hlam, hphi, ht12, p12106_1]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h0, h12096, hc01, hc23, hlam, hphi, ht12, p12106_1]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p12106_1]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p12106_1]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h12101, hlam, p12106_0]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [hlam, p12106_0]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h0, h12096, h12101, hc01, hc23, hlam, hphi, ht12, p12106_1]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p12106_1]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p12106_1]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h12102, hlam, p12106_0]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [h12103, hlam, p12106_1]
                            · have p12106_0 := h12106c.1
                              have p12106_1 := h12106c.2.1
                              have p12106_2 := h12106c.2.2.1
                              have p12106_3 := h12106c.2.2.2
                              linarith only [hlam, p12106_0]
                        · linarith only [h0, h12094, h12103, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h12039, h12102, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h11794, h11795, h12039, h12099, h12101, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12135 | h12135
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12136 | h12136
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12137 | h12137
                        · linarith only [h0, h12094, h12100, h12137, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h12094, h12137, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h12039, h12099, h12136, hlam]
                    · linarith only [h11794, h11795, h12039, h12099, h12135, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12142 | h12142
                  · linarith only [h0, h11104, h12037, h12098, h12099, h12142, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12144 | h12144
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12145 | h12145
                      · linarith only [h12099, h12145, h5135, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h12039, h12145, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h11794, h12039, h12144, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
              · linarith only [h11794, h12098, h5135, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h12150 | h12150
    · rcases m.htr 0 4 5 (by decide) (by decide) with h12151 | h12151
      · rcases m.htr 1 2 3 (by decide) (by decide) with h12152 | h12152
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12153 | h12153
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12154 | h12154
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12155 | h12155
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12156 | h12156
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12157 | h12157
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12158 | h12158
                    · linarith only [h11794, h12150, h12152, h12158, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h12152, h12155, h12158, h8661, hc01, hc12, hlam, hphi]
                  · linarith only [h11557, h12151, h12154, h12157, h6923, hc01, hc12, hlam, hphi]
                · linarith only [h11794, h12155, h12156, hc03, hc35, hlam, hphi]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12163 | h12163
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12164 | h12164
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12165 | h12165
                    · linarith only [h12152, h12155, h12165, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12167 | h12167
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12168 | h12168
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12169 | h12169
                          · rcases h2bigk with h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c | h12170c
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [hlam, p12170_0]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h0, hlam, p12170_0]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h8661, hlam, p12170_0]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h11104, hlam, p12170_0]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h11557, hlam, p12170_0]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p12170_1]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [hlam, p12170_0]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h0, h11557, h12167, hc01, hc12, hlam, hphi, p12170_1]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h0, h11557, h12165, h12167, hc01, hc12, hlam, hphi, p12170_1]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h0, h11557, hc01, hc12, hlam, hphi, p12170_1]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p12170_1]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h12152, hlam, p12170_0]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [hlam, p12170_0]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h12165, hlam, p12170_1]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h0, h11557, h12152, h12155, hc01, hc34, hlam, hphi, ht12, ht23, p12170_1]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h0, h12153, hc01, hc12, hlam, hphi, p12170_1]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h12153, hlam, p12170_0]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h12153, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12170_1]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [hlam, p12170_0]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h0, h11557, h12153, hc01, hc12, hlam, hphi, p12170_1]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h0, h12154, hc01, hc15, hlam, hphi, p12170_1]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h12154, hlam, p12170_0]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h12167, hlam, p12170_0]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [h12168, hlam, p12170_1]
                            · have p12170_0 := h12170c.1
                              have p12170_1 := h12170c.2.1
                              have p12170_2 := h12170c.2.2.1
                              have p12170_3 := h12170c.2.2.2
                              linarith only [hlam, p12170_0]
                          · linarith only [h12155, h12169, h5135, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h11104, h12150, h12151, h12155, h12168, h5135, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h12150, h12167, h8661, hlam]
                  · linarith only [h11104, h12151, h12164, h6923, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h12150, h12152, h12163, h8661, hlam]
            · linarith only [h0, h11104, h12153, h12154, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h12152, h12153, h8661, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12203 | h12203
          · linarith only [h0, h11104, h12152, h12203, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12205 | h12205
            · linarith only [h0, h11557, h12152, h12205, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12207 | h12207
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12208 | h12208
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12209 | h12209
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12210 | h12210
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12211 | h12211
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12212 | h12212
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12213 | h12213
                          · rcases h2bigk with h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c | h12214c
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [hlam, p12214_0]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h0, hlam, p12214_0]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h8661, hlam, p12214_0]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h11104, hlam, p12214_0]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h11557, hlam, p12214_0]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h0, h12205, h12210, h12212, hc01, hc23, hlam, hphi, ht12, p12214_1]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [hlam, p12214_0]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h12152, hlam, p12214_0]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h12203, hlam, p12214_0]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h12205, hlam, p12214_0]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p12214_1]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p12214_1]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [hlam, p12214_0]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h0, h11104, hc01, hc23, hlam, hphi, ht12, p12214_1]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h0, h12205, hc01, hc23, hlam, hphi, ht12, p12214_1]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p12214_1]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p12214_1]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h12210, hlam, p12214_0]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [hlam, p12214_0]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h0, h12205, h12210, hc01, hc23, hlam, hphi, ht12, p12214_1]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p12214_1]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p12214_1]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h12211, hlam, p12214_0]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [h12212, hlam, p12214_1]
                            · have p12214_0 := h12214c.1
                              have p12214_1 := h12214c.2.1
                              have p12214_2 := h12214c.2.2.1
                              have p12214_3 := h12214c.2.2.2
                              linarith only [hlam, p12214_0]
                          · linarith only [h11794, h12150, h12151, h12213, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h11794, h12150, h12151, h12152, h12203, h12207, h12212, h6923, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h11794, h12150, h12152, h12207, h12211, hlam]
                    · linarith only [h12152, h12207, h12210, hlam]
                  · linarith only [h11794, h12150, h12151, h12207, h12209, hlam]
                · linarith only [h11794, h12150, h12207, h12208, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12246 | h12246
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12247 | h12247
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12248 | h12248
                    · linarith only [h0, h12205, h12207, h12246, h12248, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h12152, h12248, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h11794, h12150, h12151, h12247, h6923, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h12150, h12246, h5135, hlam]
      · linarith only [h11794, h12150, h12151, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h12254 | h12254
      · rcases m.htr 1 2 3 (by decide) (by decide) with h12255 | h12255
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12256 | h12256
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12257 | h12257
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12258 | h12258
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12259 | h12259
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12260 | h12260
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12261 | h12261
                    · linarith only [h0, h11794, h12255, h12261, h8661, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h12258, h12261, h8661, hc01, hc13, hlam, hphi]
                  · linarith only [h12254, h12260, h6923, hlam]
                · linarith only [h11794, h12258, h12259, h8661, hc02, hc35, hlam, hphi, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12266 | h12266
                · linarith only [h0, h12150, h12258, h12266, h8661, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12268 | h12268
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12269 | h12269
                    · linarith only [h12255, h12258, h12269, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12271 | h12271
                      · linarith only [h0, h12150, h12255, h12258, h12271, h8661, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12273 | h12273
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12274 | h12274
                          · rcases h2bigk with h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c | h12275c
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [hlam, p12275_0]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h0, hlam, p12275_0]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h8661, hlam, p12275_0]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h11104, hlam, p12275_0]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h11557, hlam, p12275_0]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p12275_1]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [hlam, p12275_0]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h0, h8661, hc01, hc12, hlam, hphi, p12275_1]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h0, h11104, hc01, hc12, hlam, hphi, p12275_1]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h0, h12271, h8661, hc01, hc12, hlam, hphi, p12275_1]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p12275_1]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h12255, hlam, p12275_0]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [hlam, p12275_0]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h12269, hlam, p12275_1]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h12271, hlam, p12275_1]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h0, h12256, hc01, hc14, hlam, hphi, p12275_1]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h12256, hlam, p12275_0]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h12256, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12275_1]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [hlam, p12275_0]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h12256, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p12275_1]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p12275_1]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h12257, hlam, p12275_0]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h0, h12257, h8661, hc01, hc12, hlam, hphi, p12275_1]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [h12273, hlam, p12275_1]
                            · have p12275_0 := h12275c.1
                              have p12275_1 := h12275c.2.1
                              have p12275_2 := h12275c.2.2.1
                              have p12275_3 := h12275c.2.2.2
                              linarith only [hlam, p12275_0]
                          · linarith only [h12254, h12258, h12274, h6923, hlam]
                        · linarith only [h11104, h12254, h12273, hlam]
                  · linarith only [h11104, h12254, h12256, h12268, h6923, hc01, hc12, hlam, hphi]
            · linarith only [h0, h11104, h12256, h12257, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h12255, h12256, h8661, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12306 | h12306
          · linarith only [h0, h11104, h12255, h12306, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12308 | h12308
            · linarith only [h0, h11557, h12255, h12308, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12310 | h12310
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12311 | h12311
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12312 | h12312
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12313 | h12313
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12314 | h12314
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12315 | h12315
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12316 | h12316
                          · rcases h2bigk with h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c | h12317c
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [hlam, p12317_0]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h0, hlam, p12317_0]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h8661, hlam, p12317_0]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h11104, hlam, p12317_0]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h11557, hlam, p12317_0]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h0, h12308, h12313, h12315, hc01, hc23, hlam, hphi, ht12, p12317_1]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [hlam, p12317_0]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h12255, hlam, p12317_0]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h12306, hlam, p12317_0]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h12308, hlam, p12317_0]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p12317_1]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p12317_1]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [hlam, p12317_0]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h0, h11104, hc01, hc23, hlam, hphi, ht12, p12317_1]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h0, h12308, hc01, hc23, hlam, hphi, ht12, p12317_1]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p12317_1]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p12317_1]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h12313, hlam, p12317_0]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [hlam, p12317_0]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h0, h12308, h12313, hc01, hc23, hlam, hphi, ht12, p12317_1]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p12317_1]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p12317_1]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h12314, hlam, p12317_0]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [h12315, hlam, p12317_1]
                            · have p12317_0 := h12317c.1
                              have p12317_1 := h12317c.2.1
                              have p12317_2 := h12317c.2.2.1
                              have p12317_3 := h12317c.2.2.2
                              linarith only [hlam, p12317_0]
                          · linarith only [h0, h11104, h11794, h12254, h12313, h12316, h8661, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h12254, h12306, h12315, h6923, hlam]
                      · linarith only [h0, h11794, h12255, h12310, h12314, h8661, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h12255, h12310, h12313, hlam]
                  · linarith only [h12254, h12312, h6923, hlam]
                · linarith only [h0, h11794, h12310, h12311, h8661, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12349 | h12349
                · linarith only [h0, h12150, h12310, h12349, h8661, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12351 | h12351
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12352 | h12352
                    · linarith only [h0, h12255, h12310, h12352, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h12255, h12352, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h12254, h12351, h6923, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h12356 | h12356
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12357 | h12357
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12358 | h12358
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12359 | h12359
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12360 | h12360
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12361 | h12361
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12362 | h12362
                    · linarith only [h0, h11794, h12356, h12362, h8661, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h12359, h12362, h8661, hc01, hc13, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12365 | h12365
                    · linarith only [h0, h11794, h12356, h12365, h8661, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h12356, h12359, h12365, h8661, hc01, hc12, hlam, hphi]
                · linarith only [h0, h11794, h12359, h12360, h8661, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12369 | h12369
                · linarith only [h0, h12150, h12359, h12369, h8661, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12371 | h12371
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12372 | h12372
                    · linarith only [h12359, h12372, h5135, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12374 | h12374
                      · linarith only [h12356, h12369, h12374, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12376 | h12376
                        · linarith only [h0, h11794, h12254, h12357, h12376, h8661, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h11104, h12371, h12376, hc01, hc14, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12379 | h12379
                    · linarith only [h0, h11794, h12356, h12369, h12379, h8661, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12381 | h12381
                      · linarith only [h0, h12150, h12356, h12381, h8661, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12383 | h12383
                        · linarith only [h12359, h12371, h12383, h5135, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12385 | h12385
                          · linarith only [h0, h12356, h12359, h12371, h12385, h8661, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h12356, h12359, h12385, h8661, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h12356, h12358, h8661, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h12356, h12357, h8661, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12390 | h12390
          · linarith only [h0, h11104, h12356, h12390, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12392 | h12392
            · linarith only [h0, h11557, h12356, h12392, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12394 | h12394
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12395 | h12395
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12396 | h12396
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12397 | h12397
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12398 | h12398
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12399 | h12399
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12400 | h12400
                          · linarith only [h0, h11794, h12254, h12394, h12400, h8661, hc01, hc13, hlam, hphi]
                          · linarith only [h0, h11794, h12396, h12400, h8661, hc01, hc14, hlam, hphi]
                        · linarith only [h12390, h12396, h12399, hlam]
                      · linarith only [h12356, h12395, h12398, hlam]
                    · linarith only [h0, h12150, h12356, h12395, h12397, h8661, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12406 | h12406
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12407 | h12407
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12408 | h12408
                        · linarith only [h12396, h12408, h6923, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h12390, h12408, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h12395, h12407, h8661, hc01, hc13, hlam, hphi]
                    · linarith only [h0, h12150, h12356, h12395, h12406, h8661, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h11794, h12394, h12395, h8661, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12414 | h12414
                · linarith only [h0, h12150, h12394, h12414, h8661, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12416 | h12416
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12417 | h12417
                    · linarith only [h12394, h12417, h5135, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h12356, h12417, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12420 | h12420
                    · linarith only [h0, h12356, h12394, h12420, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h12356, h12420, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 7524000 in
set_option maxHeartbeats 7524000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s8_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7870 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8661 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h11104 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  have h6923 := hg6923
  have h7870 := hg7870
  rcases m.htr 0 2 5 (by decide) (by decide) with h11557 | h11557
  · exact r1l7_22_13_15_H_I_L_I_L_I_s8_x1_x1_x0 m hb2 hb3 hb5 hg0 hg5135 hg6923 hg7870 h8661 h11104 h11557
  · exact r1l7_22_13_15_H_I_L_I_L_I_s8_x1_x1_x1 m hb2 hb3 hb5 hg0 hg5135 hg6923 hg7870 h8661 h11104 h11557

set_option maxHeartbeats 7524000 in
set_option maxHeartbeats 7524000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s8_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7870 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8661 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  have h6923 := hg6923
  have h7870 := hg7870
  rcases m.htr 0 2 4 (by decide) (by decide) with h11104 | h11104
  · exact r1l7_22_13_15_H_I_L_I_L_I_s8_x1_x0 m hb2 hb3 hb5 hg0 hg5135 hg6923 hg7870 h8661 h11104
  · exact r1l7_22_13_15_H_I_L_I_L_I_s8_x1_x1 m hb2 hb3 hb5 hg0 hg5135 hg6923 hg7870 h8661 h11104

set_option maxHeartbeats 7524000 in
set_option maxHeartbeats 7524000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s8 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7870 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  have h6923 := hg6923
  have h7870 := hg7870
  rcases m.htr 0 2 3 (by decide) (by decide) with h8661 | h8661
  · exact r1l7_22_13_15_H_I_L_I_L_I_s8_x0 m hb2 hb3 hb5 hg0 hg5135 hg6923 hg7870 h8661
  · exact r1l7_22_13_15_H_I_L_I_L_I_s8_x1 m hb2 hb3 hb5 hg0 hg5135 hg6923 hg7870 h8661

end R2N4
