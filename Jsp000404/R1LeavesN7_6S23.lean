import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S20
import Jsp000404.R1LeavesN7_6S21
import Jsp000404.R1LeavesN7_6S22

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5504000 in
set_option maxHeartbeats 5504000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s15_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11559 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg11560 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11561 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h12797 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h12915 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h10058 := hg10058
  have h11024 := hg11024
  have h11558 := hg11558
  have h11559 := hg11559
  have h11560 := hg11560
  rcases m.htr 1 2 3 (by decide) (by decide) with h13739 | h13739
  · rcases m.htr 1 2 4 (by decide) (by decide) with h13740 | h13740
    · rcases m.htr 1 2 5 (by decide) (by decide) with h13741 | h13741
      · rcases m.htr 1 3 4 (by decide) (by decide) with h13742 | h13742
        · rcases m.htr 1 4 5 (by decide) (by decide) with h13743 | h13743
          · rcases m.htr 2 3 4 (by decide) (by decide) with h13744 | h13744
            · linarith only [h11558, h11561, h13744, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h13746 | h13746
              · linarith only [h11558, h12797, h13746, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h13748 | h13748
                · linarith only [h11559, h12915, h13748, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h13750 | h13750
                  · linarith only [h10058, h12915, h13739, h13742, h13750, hc01, hc12, hlam, hphi]
                  · linarith only [h11561, h13739, h13742, h13743, h13750, h6793, hc01, hc12, hlam, hphi]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h13753 | h13753
            · linarith only [h11558, h11561, h13753, h6793, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h13755 | h13755
              · linarith only [h11558, h12797, h13755, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h13757 | h13757
                · linarith only [h11559, h11561, h13742, h13743, h13757, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h13759 | h13759
                  · linarith only [h11024, h13739, h13742, h13743, h13759, hc01, hc12, hlam, hphi]
                  · rcases h0bigk with h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c | h13761c
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [hlam, p13761_0]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [h0, hlam, p13761_1]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [h6793, hlam, p13761_0]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [h10058, hlam, p13761_1]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [h11024, hlam, p13761_1]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      rcases p13761_3 (m.d 0 1) (by simp) with h13767 | h13767
                      · linarith only [h0, h13767, hlam]
                      · rcases p13761_3 (m.d 0 2) (by simp) with h13769 | h13769
                        · rcases p13761_3 (m.d 0 3) (by simp) with h13770 | h13770
                          · linarith only [h11558, h13770, hlam]
                          · linarith only [h13770, h6793, hlam]
                        · linarith only [h0, h13769, hlam]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [hlam, p13761_0]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      rcases p13761_3 (m.d 0 1) (by simp) with h13775 | h13775
                      · linarith only [h0, h13775, hlam]
                      · rcases p13761_3 (m.d 0 2) (by simp) with h13777 | h13777
                        · rcases p13761_3 (m.d 0 3) (by simp) with h13778 | h13778
                          · linarith only [h11558, h13778, hlam]
                          · rcases p13761_3 (m.d 0 4) (by simp) with h13780 | h13780
                            · linarith only [h11559, h13780, hlam]
                            · linarith only [h11561, h13780, hlam]
                        · linarith only [h11558, h13777, hlam]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      rcases p13761_3 (m.d 0 1) (by simp) with h13784 | h13784
                      · linarith only [h0, h13784, hlam]
                      · rcases p13761_3 (m.d 0 2) (by simp) with h13786 | h13786
                        · rcases p13761_3 (m.d 0 3) (by simp) with h13787 | h13787
                          · linarith only [h11558, h13787, hlam]
                          · rcases p13761_3 (m.d 0 4) (by simp) with h13789 | h13789
                            · linarith only [h11559, h13789, hlam]
                            · rcases p13761_3 (m.d 0 5) (by simp) with h13791 | h13791
                              · linarith only [h11560, h13791, hlam]
                              · linarith only [h12915, h13791, hlam]
                        · linarith only [h11559, h13786, hlam]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      rcases p13761_3 (m.d 0 1) (by simp) with h13795 | h13795
                      · linarith only [h0, h13795, hlam]
                      · rcases p13761_3 (m.d 0 2) (by simp) with h13797 | h13797
                        · rcases p13761_3 (m.d 0 3) (by simp) with h13798 | h13798
                          · linarith only [h11558, h13798, hlam]
                          · rcases p13761_3 (m.d 0 4) (by simp) with h13800 | h13800
                            · linarith only [h11559, h13800, hlam]
                            · rcases p13761_3 (m.d 0 5) (by simp) with h13802 | h13802
                              · linarith only [h11560, h13802, hlam]
                              · rcases h0emin with h13804 | h13804 | h13804 | h13804 | h13804
                                · linarith only [h11561, h12915, h13804, h6793, hlam, p13761_1, u0elo1]
                                · rcases h2bigk with h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c | h13806c
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [hlam, p13806_0]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [h0, hlam, p13806_1]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    rcases p13806_3 (m.d 0 2) (by simp) with h13809 | h13809
                                    · rcases p13806_3 (m.d 1 2) (by simp) with h13810 | h13810
                                      · rcases p13806_3 (m.d 2 3) (by simp) with h13811 | h13811
                                        · linarith only [h13811, hlam, p13806_0]
                                        · rcases p13806_3 (m.d 2 4) (by simp) with h13813 | h13813
                                          · linarith only [h11559, h13813, hlam]
                                          · linarith only [h13753, h13813, hlam]
                                      · linarith only [h13739, h13810, hlam]
                                    · linarith only [h13809, hlam, p13806_0]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    rcases p13806_3 (m.d 0 2) (by simp) with h13818 | h13818
                                    · rcases p13806_3 (m.d 1 2) (by simp) with h13819 | h13819
                                      · rcases p13806_3 (m.d 2 3) (by simp) with h13820 | h13820
                                        · linarith only [h11558, h13820, hlam]
                                        · rcases p13806_3 (m.d 2 4) (by simp) with h13822 | h13822
                                          · linarith only [h13822, hlam, p13806_0]
                                          · rcases p13806_3 (m.d 2 5) (by simp) with h13824 | h13824
                                            · linarith only [h11560, h13824, hlam]
                                            · linarith only [h13757, h13824, hlam]
                                      · linarith only [h13740, h13819, hlam]
                                    · linarith only [h13818, hlam, p13806_0]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    rcases p13806_3 (m.d 0 2) (by simp) with h13829 | h13829
                                    · rcases p13806_3 (m.d 1 2) (by simp) with h13830 | h13830
                                      · rcases p13806_3 (m.d 2 3) (by simp) with h13831 | h13831
                                        · linarith only [h11558, h13831, hlam]
                                        · rcases p13806_3 (m.d 2 4) (by simp) with h13833 | h13833
                                          · linarith only [h11559, h13833, hlam]
                                          · rcases p13806_3 (m.d 2 5) (by simp) with h13835 | h13835
                                            · linarith only [h13835, hlam, p13806_0]
                                            · rcases h4bigk with h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h10058, hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h12915, hc24, hlam, hphi, ht0b, ht45, ht5b, p13761_1, p13837_1, u0elo1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h11561, hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h12915, hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h11561, h13743, h6793, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13743, hc24, hc45, hlam, hphi, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h11561, h13743, h6793, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13743, hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h11559, hlam, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13740, hlam, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13753, hlam, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13757, hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h11561, h13742, h6793, hc01, hc13, hlam, hphi, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13742, hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13742, h13743, hc24, hc45, hlam, hphi, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13759, hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                rcases p13837_3 (m.d 0 4) (by simp) with h13858 | h13858
                                                · linarith only [h13858, hlam, p13837_0]
                                                · rcases p13837_3 (m.d 1 4) (by simp) with h13860 | h13860
                                                  · linarith only [h13743, h13860, hlam]
                                                  · linarith only [h10058, h13860, hlam]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h10058, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                rcases p13837_3 (m.d 0 4) (by simp) with h13864 | h13864
                                                · linarith only [h12915, h13864, hlam]
                                                · linarith only [h11559, h13864, hlam]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h11561, h6793, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [hlam, p13837_0]
                                      · linarith only [h13741, h13830, hlam]
                                    · linarith only [h13829, hlam, p13806_0]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [h11561, h12915, h6793, hc01, hc12, hlam, hphi, p13761_1, p13806_1]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [hlam, p13806_0]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    rcases p13806_3 (m.d 0 2) (by simp) with h13873 | h13873
                                    · linarith only [h0, h13873, hlam]
                                    · linarith only [h11558, h13873, hlam]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    rcases p13806_3 (m.d 0 2) (by simp) with h13876 | h13876
                                    · linarith only [h0, h13876, hlam]
                                    · linarith only [h11559, h13876, hlam]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    rcases p13806_3 (m.d 0 2) (by simp) with h13879 | h13879
                                    · linarith only [h0, h13879, hlam]
                                    · linarith only [h11560, h13879, hlam]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [h11558, hlam, p13806_0]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [h13739, hlam, p13806_0]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [hlam, p13806_0]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [h13753, hlam, p13806_0]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [h13755, hlam, p13806_0]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [h11559, hlam, p13806_0]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [h13740, hlam, p13806_0]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [h11559, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13806_1, u0elo1]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [hlam, p13806_0]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [h13757, hlam, p13806_1]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [h11560, hlam, p13806_0]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [h13741, hlam, p13806_0]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [h11560, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13806_1, u0elo1]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [h11560, hc24, hlam, hphi, ht0b, ht45, ht5b, p13761_1, p13806_1, u0elo1]
                                  · have p13806_0 := h13806c.1
                                    have p13806_1 := h13806c.2.1
                                    have p13806_2 := h13806c.2.2.1
                                    have p13806_3 := h13806c.2.2.2
                                    linarith only [hlam, p13806_0]
                                · linarith only [h12797, h13804, hlam, p13761_1, u0elo1]
                                · linarith only [h12915, h13804, hlam, p13761_1, u0elo1]
                                · linarith only [h13804, hlam, p13761_1, u0elo1]
                        · linarith only [h11560, h13797, hlam]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [h11561, hc01, hc34, hlam, hphi, ht12, ht23, p13761_1]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [h11558, hlam, p13761_1]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [hlam, p13761_0]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [h11561, hlam, p13761_1]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [h12797, hlam, p13761_1]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [h12915, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13761_1]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [h11559, hlam, p13761_0]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [h12915, hc03, hc45, hlam, hphi, ht34, p13761_1]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [hlam, p13761_0]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [h12915, hlam, p13761_0]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      rcases p13761_3 (m.d 0 1) (by simp) with h13911 | h13911
                      · linarith only [h11024, h13911, hlam]
                      · rcases p13761_3 (m.d 0 2) (by simp) with h13913 | h13913
                        · rcases p13761_3 (m.d 0 3) (by simp) with h13914 | h13914
                          · linarith only [h12797, h13914, hlam]
                          · linarith only [h13914, h6793, hlam]
                        · linarith only [h0, h13913, hlam]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [h11560, hlam, p13761_1]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      rcases p13761_3 (m.d 0 1) (by simp) with h13919 | h13919
                      · linarith only [h11024, h13919, hlam]
                      · rcases p13761_3 (m.d 0 2) (by simp) with h13921 | h13921
                        · rcases p13761_3 (m.d 0 3) (by simp) with h13922 | h13922
                          · linarith only [h12797, h13922, hlam]
                          · rcases p13761_3 (m.d 0 4) (by simp) with h13924 | h13924
                            · linarith only [h12915, h13924, hlam]
                            · linarith only [h11561, h13924, hlam]
                        · linarith only [h11558, h13921, hlam]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      rcases p13761_3 (m.d 0 1) (by simp) with h13928 | h13928
                      · linarith only [h11024, h13928, hlam]
                      · rcases p13761_3 (m.d 0 2) (by simp) with h13930 | h13930
                        · rcases p13761_3 (m.d 0 3) (by simp) with h13931 | h13931
                          · linarith only [h12797, h13931, hlam]
                          · rcases p13761_3 (m.d 0 4) (by simp) with h13933 | h13933
                            · linarith only [h12915, h13933, hlam]
                            · rcases p13761_3 (m.d 0 5) (by simp) with h13935 | h13935
                              · rcases h0emin with h13936 | h13936 | h13936 | h13936 | h13936
                                · linarith only [h11561, h13936, h6793, hlam, p13761_1, u0elo4]
                                · rcases h2bigk with h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [hlam, p13938_0]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [h0, hlam, p13938_1]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    rcases p13938_3 (m.d 0 2) (by simp) with h13941 | h13941
                                    · rcases p13938_3 (m.d 1 2) (by simp) with h13942 | h13942
                                      · rcases p13938_3 (m.d 2 3) (by simp) with h13943 | h13943
                                        · linarith only [h13943, hlam, p13938_0]
                                        · rcases p13938_3 (m.d 2 4) (by simp) with h13945 | h13945
                                          · linarith only [h11559, h13945, hlam]
                                          · linarith only [h13753, h13945, hlam]
                                      · linarith only [h13739, h13942, hlam]
                                    · linarith only [h13941, hlam, p13938_0]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    rcases p13938_3 (m.d 0 2) (by simp) with h13950 | h13950
                                    · rcases p13938_3 (m.d 1 2) (by simp) with h13951 | h13951
                                      · rcases p13938_3 (m.d 2 3) (by simp) with h13952 | h13952
                                        · linarith only [h11558, h13952, hlam]
                                        · rcases p13938_3 (m.d 2 4) (by simp) with h13954 | h13954
                                          · linarith only [h13954, hlam, p13938_0]
                                          · rcases p13938_3 (m.d 2 5) (by simp) with h13956 | h13956
                                            · linarith only [h11560, h13956, hlam]
                                            · linarith only [h13757, h13956, hlam]
                                      · linarith only [h13740, h13951, hlam]
                                    · linarith only [h13950, hlam, p13938_0]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    rcases p13938_3 (m.d 0 2) (by simp) with h13961 | h13961
                                    · rcases p13938_3 (m.d 1 2) (by simp) with h13962 | h13962
                                      · rcases p13938_3 (m.d 2 3) (by simp) with h13963 | h13963
                                        · linarith only [h11558, h13963, hlam]
                                        · rcases p13938_3 (m.d 2 4) (by simp) with h13965 | h13965
                                          · linarith only [h11559, h13965, hlam]
                                          · rcases p13938_3 (m.d 2 5) (by simp) with h13967 | h13967
                                            · linarith only [h13967, hlam, p13938_0]
                                            · rcases h4bigk with h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c | h13969c
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [hlam, p13969_0]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h10058, hlam, p13969_0]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h11560, h13753, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13761_1, p13969_1, u0elo1]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h11561, hlam, p13969_0]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h12915, hlam, p13969_0]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h13743, hc04, hc45, hlam, hphi, p13969_1]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [hlam, p13969_0]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h13743, h13753, hc23, hc45, hlam, hphi, ht34, p13969_1]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h13743, hc34, hc45, hlam, hphi, p13969_1]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h13743, hlam, p13969_0]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h11559, hlam, p13969_1]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h13740, hlam, p13969_1]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [hlam, p13969_0]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h13753, hlam, p13969_1]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h13757, hlam, p13969_0]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h11561, h13739, h13742, h6793, hc01, hc12, hlam, hphi, p13969_1]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h13742, hlam, p13969_0]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h13742, h13743, h13753, hc23, hc45, hlam, hphi, ht34, p13969_1]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [hlam, p13969_0]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h13759, hlam, p13969_0]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                rcases p13969_3 (m.d 0 4) (by simp) with h13990 | h13990
                                                · linarith only [h13990, hlam, p13969_0]
                                                · rcases p13969_3 (m.d 1 4) (by simp) with h13992 | h13992
                                                  · linarith only [h13743, h13992, hlam]
                                                  · linarith only [h10058, h13992, hlam]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h10058, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13969_1]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                rcases p13969_3 (m.d 0 4) (by simp) with h13996 | h13996
                                                · linarith only [h12915, h13996, hlam]
                                                · linarith only [h11559, h13996, hlam]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [h11561, h6793, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13969_1]
                                              · have p13969_0 := h13969c.1
                                                have p13969_1 := h13969c.2.1
                                                have p13969_2 := h13969c.2.2.1
                                                have p13969_3 := h13969c.2.2.2
                                                linarith only [hlam, p13969_0]
                                      · linarith only [h13741, h13962, hlam]
                                    · linarith only [h13961, hlam, p13938_0]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [h13936, hc12, hlam, ht01, p13938_1]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [hlam, p13938_0]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    rcases p13938_3 (m.d 0 2) (by simp) with h14005 | h14005
                                    · linarith only [h0, h14005, hlam]
                                    · linarith only [h11558, h14005, hlam]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    rcases p13938_3 (m.d 0 2) (by simp) with h14008 | h14008
                                    · linarith only [h0, h14008, hlam]
                                    · linarith only [h11559, h14008, hlam]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    rcases p13938_3 (m.d 0 2) (by simp) with h14011 | h14011
                                    · linarith only [h0, h14011, hlam]
                                    · linarith only [h11560, h14011, hlam]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [h11558, hlam, p13938_0]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [h13739, hlam, p13938_0]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [hlam, p13938_0]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [h13753, hlam, p13938_0]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [h13755, hlam, p13938_0]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [h11559, hlam, p13938_0]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [h13740, hlam, p13938_0]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [h11559, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13938_1, u0elo1]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [hlam, p13938_0]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [h13757, hlam, p13938_1]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [h11560, hlam, p13938_0]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [h13741, hlam, p13938_0]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [h11560, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13938_1, u0elo1]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [h11560, hc24, hlam, hphi, ht0b, ht45, ht5b, p13938_1, u0elo1]
                                  · have p13938_0 := h13938c.1
                                    have p13938_1 := h13938c.2.1
                                    have p13938_2 := h13938c.2.2.1
                                    have p13938_3 := h13938c.2.2.2
                                    linarith only [hlam, p13938_0]
                                · linarith only [h11561, h13936, hlam, p13761_1, u0elo4]
                                · linarith only [h13936, hlam, p13761_1, u0elo4]
                                · rcases h2bigk with h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c | h14031c
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [hlam, p14031_0]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [h0, hlam, p14031_1]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    rcases p14031_3 (m.d 0 2) (by simp) with h14034 | h14034
                                    · rcases p14031_3 (m.d 1 2) (by simp) with h14035 | h14035
                                      · rcases p14031_3 (m.d 2 3) (by simp) with h14036 | h14036
                                        · linarith only [h14036, hlam, p14031_0]
                                        · rcases p14031_3 (m.d 2 4) (by simp) with h14038 | h14038
                                          · linarith only [h11559, h14038, hlam]
                                          · linarith only [h13753, h14038, hlam]
                                      · linarith only [h13739, h14035, hlam]
                                    · linarith only [h14034, hlam, p14031_0]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    rcases p14031_3 (m.d 0 2) (by simp) with h14043 | h14043
                                    · rcases p14031_3 (m.d 1 2) (by simp) with h14044 | h14044
                                      · rcases p14031_3 (m.d 2 3) (by simp) with h14045 | h14045
                                        · linarith only [h11558, h14045, hlam]
                                        · rcases p14031_3 (m.d 2 4) (by simp) with h14047 | h14047
                                          · linarith only [h14047, hlam, p14031_0]
                                          · rcases p14031_3 (m.d 2 5) (by simp) with h14049 | h14049
                                            · linarith only [h11560, h14049, hlam]
                                            · linarith only [h13757, h14049, hlam]
                                      · linarith only [h13740, h14044, hlam]
                                    · linarith only [h14043, hlam, p14031_0]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    rcases p14031_3 (m.d 0 2) (by simp) with h14054 | h14054
                                    · rcases p14031_3 (m.d 1 2) (by simp) with h14055 | h14055
                                      · rcases p14031_3 (m.d 2 3) (by simp) with h14056 | h14056
                                        · linarith only [h11558, h14056, hlam]
                                        · rcases p14031_3 (m.d 2 4) (by simp) with h14058 | h14058
                                          · linarith only [h11559, h14058, hlam]
                                          · rcases p14031_3 (m.d 2 5) (by simp) with h14060 | h14060
                                            · linarith only [h14060, hlam, p14031_0]
                                            · rcases h4bigk with h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c | h14062c
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [hlam, p14062_0]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h10058, hlam, p14062_0]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h11560, h13753, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13761_1, p14062_1, u0elo1]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h11561, hlam, p14062_0]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h12915, hlam, p14062_0]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h11561, h13743, h6793, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14062_1]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [hlam, p14062_0]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h13743, h13753, hc23, hc45, hlam, hphi, ht34, p14062_1]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h11561, h13743, h6793, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14062_1]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h13743, hlam, p14062_0]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h11559, hlam, p14062_1]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h13740, hlam, p14062_1]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [hlam, p14062_0]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h13753, hlam, p14062_1]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h13757, hlam, p14062_0]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h11561, h13739, h13742, h6793, hc01, hc12, hlam, hphi, p14062_1]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h13742, hlam, p14062_0]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h13742, h13743, h13753, hc23, hc45, hlam, hphi, ht34, p14062_1]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [hlam, p14062_0]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h13759, hlam, p14062_0]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                rcases p14062_3 (m.d 0 4) (by simp) with h14083 | h14083
                                                · linarith only [h14083, hlam, p14062_0]
                                                · rcases p14062_3 (m.d 1 4) (by simp) with h14085 | h14085
                                                  · linarith only [h13743, h14085, hlam]
                                                  · linarith only [h10058, h14085, hlam]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h10058, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14062_1]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                rcases p14062_3 (m.d 0 4) (by simp) with h14089 | h14089
                                                · linarith only [h12915, h14089, hlam]
                                                · linarith only [h11559, h14089, hlam]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [h11561, h6793, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14062_1]
                                              · have p14062_0 := h14062c.1
                                                have p14062_1 := h14062c.2.1
                                                have p14062_2 := h14062c.2.2.1
                                                have p14062_3 := h14062c.2.2.2
                                                linarith only [hlam, p14062_0]
                                      · linarith only [h13741, h14055, hlam]
                                    · linarith only [h14054, hlam, p14031_0]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [h11560, h13936, hc12, hlam, ht01, p14031_1]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [hlam, p14031_0]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    rcases p14031_3 (m.d 0 2) (by simp) with h14098 | h14098
                                    · linarith only [h0, h14098, hlam]
                                    · linarith only [h11558, h14098, hlam]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    rcases p14031_3 (m.d 0 2) (by simp) with h14101 | h14101
                                    · linarith only [h0, h14101, hlam]
                                    · linarith only [h11559, h14101, hlam]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    rcases p14031_3 (m.d 0 2) (by simp) with h14104 | h14104
                                    · linarith only [h0, h14104, hlam]
                                    · linarith only [h11560, h14104, hlam]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [h11558, hlam, p14031_0]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [h13739, hlam, p14031_0]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [hlam, p14031_0]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [h13753, hlam, p14031_0]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [h13755, hlam, p14031_0]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [h11559, hlam, p14031_0]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [h13740, hlam, p14031_0]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [h11559, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14031_1, u0elo1]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [hlam, p14031_0]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [h13757, hlam, p14031_1]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [h11560, hlam, p14031_0]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [h13741, hlam, p14031_0]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [h11560, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14031_1, u0elo1]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [h11560, hc24, hlam, hphi, ht0b, ht45, ht5b, p14031_1, u0elo1]
                                  · have p14031_0 := h14031c.1
                                    have p14031_1 := h14031c.2.1
                                    have p14031_2 := h14031c.2.2.1
                                    have p14031_3 := h14031c.2.2.2
                                    linarith only [hlam, p14031_0]
                              · linarith only [h12915, h13935, hlam]
                        · linarith only [h11559, h13930, hlam]
                    · have p13761_0 := h13761c.1
                      have p13761_1 := h13761c.2.1
                      have p13761_2 := h13761c.2.2.1
                      have p13761_3 := h13761c.2.2.2
                      linarith only [hlam, p13761_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h14125 | h14125
          · rcases m.htr 2 3 4 (by decide) (by decide) with h14126 | h14126
            · linarith only [h13742, h14126, h6793, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h14128 | h14128
              · linarith only [h11558, h12797, h14128, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h14130 | h14130
                · linarith only [h11559, h11561, h12915, h14130, h6793, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h14132 | h14132
                  · rcases h0bigk with h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c | h14133c
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [hlam, p14133_0]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [h0, hlam, p14133_1]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [h6793, hlam, p14133_0]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [h10058, hlam, p14133_1]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [h11024, hlam, p14133_1]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      rcases p14133_3 (m.d 0 1) (by simp) with h14139 | h14139
                      · linarith only [h0, h14139, hlam]
                      · rcases p14133_3 (m.d 0 2) (by simp) with h14141 | h14141
                        · rcases p14133_3 (m.d 0 3) (by simp) with h14142 | h14142
                          · linarith only [h11558, h14142, hlam]
                          · linarith only [h14142, h6793, hlam]
                        · linarith only [h0, h14141, hlam]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [hlam, p14133_0]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      rcases p14133_3 (m.d 0 1) (by simp) with h14147 | h14147
                      · linarith only [h0, h14147, hlam]
                      · rcases p14133_3 (m.d 0 2) (by simp) with h14149 | h14149
                        · rcases p14133_3 (m.d 0 3) (by simp) with h14150 | h14150
                          · linarith only [h11558, h14150, hlam]
                          · rcases p14133_3 (m.d 0 4) (by simp) with h14152 | h14152
                            · linarith only [h11559, h14152, hlam]
                            · linarith only [h11561, h14152, hlam]
                        · linarith only [h11558, h14149, hlam]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      rcases p14133_3 (m.d 0 1) (by simp) with h14156 | h14156
                      · linarith only [h0, h14156, hlam]
                      · rcases p14133_3 (m.d 0 2) (by simp) with h14158 | h14158
                        · rcases p14133_3 (m.d 0 3) (by simp) with h14159 | h14159
                          · linarith only [h11558, h14159, hlam]
                          · rcases p14133_3 (m.d 0 4) (by simp) with h14161 | h14161
                            · linarith only [h11559, h14161, hlam]
                            · rcases p14133_3 (m.d 0 5) (by simp) with h14163 | h14163
                              · linarith only [h11560, h14163, hlam]
                              · linarith only [h12915, h14163, hlam]
                        · linarith only [h11559, h14158, hlam]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      rcases p14133_3 (m.d 0 1) (by simp) with h14167 | h14167
                      · linarith only [h0, h14167, hlam]
                      · rcases p14133_3 (m.d 0 2) (by simp) with h14169 | h14169
                        · rcases p14133_3 (m.d 0 3) (by simp) with h14170 | h14170
                          · linarith only [h11558, h14170, hlam]
                          · rcases p14133_3 (m.d 0 4) (by simp) with h14172 | h14172
                            · linarith only [h11559, h14172, hlam]
                            · rcases p14133_3 (m.d 0 5) (by simp) with h14174 | h14174
                              · linarith only [h11560, h14174, hlam]
                              · rcases h0emin with h14176 | h14176 | h14176 | h14176 | h14176
                                · linarith only [h11561, h12915, h14125, h14176, h6793, hc14, hlam, ht01]
                                · rcases h2bigk with h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c | h14178c
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [hlam, p14178_0]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [h0, hlam, p14178_1]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    rcases p14178_3 (m.d 0 2) (by simp) with h14181 | h14181
                                    · rcases p14178_3 (m.d 1 2) (by simp) with h14182 | h14182
                                      · rcases p14178_3 (m.d 2 3) (by simp) with h14183 | h14183
                                        · linarith only [h14183, hlam, p14178_0]
                                        · rcases p14178_3 (m.d 2 4) (by simp) with h14185 | h14185
                                          · linarith only [h11559, h14185, hlam]
                                          · linarith only [h14126, h14185, hlam]
                                      · linarith only [h13739, h14182, hlam]
                                    · linarith only [h14181, hlam, p14178_0]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    rcases p14178_3 (m.d 0 2) (by simp) with h14190 | h14190
                                    · rcases p14178_3 (m.d 1 2) (by simp) with h14191 | h14191
                                      · rcases p14178_3 (m.d 2 3) (by simp) with h14192 | h14192
                                        · linarith only [h11558, h14192, hlam]
                                        · rcases p14178_3 (m.d 2 4) (by simp) with h14194 | h14194
                                          · linarith only [h14194, hlam, p14178_0]
                                          · rcases p14178_3 (m.d 2 5) (by simp) with h14196 | h14196
                                            · linarith only [h11560, h14196, hlam]
                                            · linarith only [h14130, h14196, hlam]
                                      · linarith only [h13740, h14191, hlam]
                                    · linarith only [h14190, hlam, p14178_0]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    rcases p14178_3 (m.d 0 2) (by simp) with h14201 | h14201
                                    · rcases p14178_3 (m.d 1 2) (by simp) with h14202 | h14202
                                      · rcases p14178_3 (m.d 2 3) (by simp) with h14203 | h14203
                                        · linarith only [h11558, h14203, hlam]
                                        · rcases p14178_3 (m.d 2 4) (by simp) with h14205 | h14205
                                          · linarith only [h11559, h14205, hlam]
                                          · rcases p14178_3 (m.d 2 5) (by simp) with h14207 | h14207
                                            · linarith only [h14207, hlam, p14178_0]
                                            · rcases h4bigk with h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c | h14209c
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [hlam, p14209_0]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [h10058, hlam, p14209_0]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [h12915, hc24, hlam, hphi, ht0b, ht45, ht5b, p14133_1, p14209_1, u0elo1]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [h11561, hlam, p14209_0]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [h12915, hlam, p14209_0]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                rcases p14209_3 (m.d 0 4) (by simp) with h14215 | h14215
                                                · linarith only [h10058, h14215, hlam]
                                                · rcases p14209_3 (m.d 1 4) (by simp) with h14217 | h14217
                                                  · rcases p14209_3 (m.d 2 4) (by simp) with h14218 | h14218
                                                    · linarith only [h13740, h14218, hlam]
                                                    · rcases p14209_3 (m.d 3 4) (by simp) with h14220 | h14220
                                                      · rcases p14209_3 (m.d 4 5) (by simp) with h14221 | h14221
                                                        · linarith only [h14125, h14221, hlam]
                                                        · linarith only [h12915, h14221, hlam]
                                                      · linarith only [h11561, h14220, hlam]
                                                  · linarith only [h10058, h14217, hlam]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [hlam, p14209_0]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                rcases p14209_3 (m.d 0 4) (by simp) with h14227 | h14227
                                                · linarith only [h10058, h14227, hlam]
                                                · linarith only [h11559, h14227, hlam]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [h13742, hlam, p14209_1]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [h11561, h12915, h13742, h6793, hc01, hc34, hlam, hphi, ht12, ht23, p14209_1]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [h11559, hlam, p14209_1]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [h13740, hlam, p14209_1]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [hlam, p14209_0]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [h14126, hlam, p14209_1]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [h14130, hlam, p14209_0]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                rcases p14209_3 (m.d 0 4) (by simp) with h14237 | h14237
                                                · linarith only [h11561, h14237, hlam]
                                                · rcases p14209_3 (m.d 1 4) (by simp) with h14239 | h14239
                                                  · linarith only [h13742, h14239, hlam]
                                                  · linarith only [h10058, h14239, hlam]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [h10058, hc01, hc34, hlam, hphi, ht12, ht23, p14209_1]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                rcases p14209_3 (m.d 0 4) (by simp) with h14243 | h14243
                                                · linarith only [h11561, h14243, hlam]
                                                · linarith only [h11559, h14243, hlam]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [hlam, p14209_0]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [h11561, h12915, h6793, hc01, hc34, hlam, hphi, ht12, ht23, p14209_1]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [h11561, h14125, h6793, hc01, hc14, hlam, hphi, p14209_1]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [h14125, hlam, p14209_0]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [h13742, h14125, h14126, hc23, hc34, hlam, hphi, p14209_1]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [h14132, hlam, p14209_0]
                                              · have p14209_0 := h14209c.1
                                                have p14209_1 := h14209c.2.1
                                                have p14209_2 := h14209c.2.2.1
                                                have p14209_3 := h14209c.2.2.2
                                                linarith only [hlam, p14209_0]
                                      · linarith only [h13741, h14202, hlam]
                                    · linarith only [h14201, hlam, p14178_0]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [h11561, h12915, h6793, hc01, hc12, hlam, hphi, p14133_1, p14178_1]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [hlam, p14178_0]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    rcases p14178_3 (m.d 0 2) (by simp) with h14257 | h14257
                                    · linarith only [h0, h14257, hlam]
                                    · linarith only [h11558, h14257, hlam]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    rcases p14178_3 (m.d 0 2) (by simp) with h14260 | h14260
                                    · linarith only [h0, h14260, hlam]
                                    · linarith only [h11559, h14260, hlam]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    rcases p14178_3 (m.d 0 2) (by simp) with h14263 | h14263
                                    · linarith only [h0, h14263, hlam]
                                    · linarith only [h11560, h14263, hlam]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [h11558, hlam, p14178_0]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [h13739, hlam, p14178_0]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [hlam, p14178_0]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [h14126, hlam, p14178_0]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [h14128, hlam, p14178_0]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [h11559, hlam, p14178_0]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [h13740, hlam, p14178_0]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [h11559, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14178_1, u0elo1]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [hlam, p14178_0]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [h14130, hlam, p14178_1]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [h11560, hlam, p14178_0]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [h13741, hlam, p14178_0]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [h11560, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14178_1, u0elo1]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [h11560, hc24, hlam, hphi, ht0b, ht45, ht5b, p14133_1, p14178_1, u0elo1]
                                  · have p14178_0 := h14178c.1
                                    have p14178_1 := h14178c.2.1
                                    have p14178_2 := h14178c.2.2.1
                                    have p14178_3 := h14178c.2.2.2
                                    linarith only [hlam, p14178_0]
                                · linarith only [h12797, h14176, hlam, p14133_1, u0elo1]
                                · linarith only [h12915, h13742, h14125, h14176, hc34, hlam, ht01, ht12, ht23]
                                · linarith only [h14176, hlam, p14133_1, u0elo1]
                        · linarith only [h11560, h14169, hlam]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [h12797, hc01, hc35, hlam, hphi, ht12, ht23, p14133_1]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [h11558, hlam, p14133_1]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [hlam, p14133_0]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [h11561, hlam, p14133_1]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [h12797, hlam, p14133_1]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [h12915, h13742, h14125, hc01, hc34, hlam, hphi, ht12, ht23, p14133_1]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [h11559, hlam, p14133_0]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [h12915, h13742, h14125, hc03, hc34, hlam, hphi, p14133_1]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [hlam, p14133_0]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [h12915, hlam, p14133_0]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [h12915, h13742, h14125, hc01, hc34, hlam, hphi, ht12, ht23, p14133_1]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [h11560, hlam, p14133_1]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [h12915, h13742, h14125, h6793, hc01, hc34, hlam, hphi, ht12, ht23, p14133_1]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [h10058, h12915, h13742, h14125, hc01, hc34, hlam, hphi, ht12, ht23, p14133_1]
                    · have p14133_0 := h14133c.1
                      have p14133_1 := h14133c.2.1
                      have p14133_2 := h14133c.2.2.1
                      have p14133_3 := h14133c.2.2.2
                      linarith only [hlam, p14133_0]
                  · linarith only [h13742, h14125, h14132, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h14301 | h14301
            · linarith only [h11558, h11561, h14301, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h14303 | h14303
              · linarith only [h11558, h12797, h14303, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h14305 | h14305
                · linarith only [h11559, h14125, h14305, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h14307 | h14307
                  · linarith only [h10058, h14125, h14307, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h13742, h14307, h6793, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
      · linarith only [h0, h11560, h13741, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
    · linarith only [h0, h11559, h13740, hlam]
  · linarith only [h0, h11558, h13739, hlam]

set_option maxHeartbeats 5504000 in
set_option maxHeartbeats 5504000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s15_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11559 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg11560 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11561 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h12797 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h10058 := hg10058
  have h11024 := hg11024
  have h11558 := hg11558
  have h11559 := hg11559
  have h11560 := hg11560
  rcases m.htr 0 4 5 (by decide) (by decide) with h12915 | h12915
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s15_x1_x1_x0 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 hg11558 hg11559 hg11560 h11561 h12797 h12915
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s15_x1_x1_x1 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 hg11558 hg11559 hg11560 h11561 h12797 h12915

set_option maxHeartbeats 5504000 in
set_option maxHeartbeats 5504000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s15_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11559 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg11560 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11561 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h10058 := hg10058
  have h11024 := hg11024
  have h11558 := hg11558
  have h11559 := hg11559
  have h11560 := hg11560
  rcases m.htr 0 3 5 (by decide) (by decide) with h12797 | h12797
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s15_x1_x0 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 hg11558 hg11559 hg11560 h11561 h12797
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s15_x1_x1 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 hg11558 hg11559 hg11560 h11561 h12797

set_option maxHeartbeats 5504000 in
set_option maxHeartbeats 5504000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s15 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11559 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg11560 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h10058 := hg10058
  have h11024 := hg11024
  have h11558 := hg11558
  have h11559 := hg11559
  have h11560 := hg11560
  rcases m.htr 0 3 4 (by decide) (by decide) with h11561 | h11561
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s15_x0 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 hg11558 hg11559 hg11560 h11561
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s15_x1 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 hg11558 hg11559 hg11560 h11561

set_option maxHeartbeats 5734000 in
set_option maxHeartbeats 5734000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s14 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11559 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h10058 := hg10058
  have h11024 := hg11024
  have h11558 := hg11558
  have h11559 := hg11559
  rcases m.htr 0 2 5 (by decide) (by decide) with h11560 | h11560
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s15 m hb0 hb2 hb4 h0 h6793 h10058 h11024 h11558 h11559 h11560
  · rcases m.htr 0 3 4 (by decide) (by decide) with h14313 | h14313
    · rcases m.htr 0 3 5 (by decide) (by decide) with h14314 | h14314
      · linarith only [h11558, h11560, h14314, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h14316 | h14316
        · linarith only [h11558, h11560, h14313, h14316, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14318 | h14318
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14319 | h14319
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14320 | h14320
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14321 | h14321
                · rcases m.htr 1 4 5 (by decide) (by decide) with h14322 | h14322
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14323 | h14323
                    · linarith only [h11558, h11560, h14320, h14323, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h11558, h11560, h14313, h14320, h14323, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14326 | h14326
                    · linarith only [h11558, h11560, h14320, h14326, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h11558, h11560, h14313, h14320, h14326, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h11558, h11560, h14313, h14320, h14321, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14330 | h14330
                · rcases m.htr 1 4 5 (by decide) (by decide) with h14331 | h14331
                  · linarith only [h10058, h14316, h14318, h14320, h14330, h14331, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14333 | h14333
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14334 | h14334
                      · linarith only [h11558, h11560, h14314, h14334, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14336 | h14336
                        · linarith only [h10058, h14331, h14336, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h11558, h14320, h14333, h14336, hc34, hc45, hlam, hphi]
                    · linarith only [h14313, h14314, h14333, hc23, hc35, hlam, hphi]
                · linarith only [h14313, h14330, h6793, hlam]
            · linarith only [h11559, h11560, h14313, h14318, h14319, h6793, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
          · linarith only [h0, h11558, h14318, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h14343 | h14343
      · linarith only [h11558, h11560, h14343, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h14345 | h14345
        · linarith only [h11559, h11560, h14345, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14347 | h14347
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14348 | h14348
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14349 | h14349
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14350 | h14350
                · rcases m.htr 1 4 5 (by decide) (by decide) with h14351 | h14351
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14352 | h14352
                    · linarith only [h11558, h14313, h14352, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14354 | h14354
                      · linarith only [h11559, h11560, h14343, h14349, h14352, h14354, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14356 | h14356
                        · linarith only [h11559, h11560, h14345, h14349, h14356, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h14358 | h14358
                          · linarith only [h11559, h11560, h14352, h14356, h14358, hc23, hc34, hlam, hphi]
                          · linarith only [h14313, h14347, h14350, h14351, h14358, h6793, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14361 | h14361
                    · linarith only [h11558, h14313, h14361, h6793, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14363 | h14363
                      · linarith only [h11559, h11560, h14349, h14361, h14363, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14365 | h14365
                        · linarith only [h11559, h11560, h14349, h14351, h14365, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h14367 | h14367
                          · linarith only [h14350, h14351, h14367, hlam]
                          · rcases h0bigk with h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c | h14369c
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [hlam, p14369_0]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h0, hlam, p14369_1]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h6793, hlam, p14369_0]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h10058, hlam, p14369_1]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h11024, hlam, p14369_1]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h11560, h14349, hc01, hc12, hlam, hphi, p14369_1]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [hlam, p14369_0]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h11560, h14349, h6793, hc01, hc12, hlam, hphi, p14369_1]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h11560, h14313, h14349, h6793, hc01, hc12, hlam, hphi, p14369_1]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h11560, hlam, p14369_0]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h14313, h14350, hc01, hc14, hlam, hphi, p14369_1]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h11558, hlam, p14369_1]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [hlam, p14369_0]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h14313, hlam, p14369_1]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h14343, hlam, p14369_1]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h10058, h14351, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14369_1]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h11559, hlam, p14369_0]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h10058, h14351, hc03, hc45, hlam, hphi, ht34, p14369_1]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [hlam, p14369_0]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h14345, hlam, p14369_0]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h11560, h14349, hc01, hc12, hlam, hphi, p14369_1]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h11559, h11560, h14349, h14361, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14369_1]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h11560, h14349, h6793, hc01, hc12, hlam, hphi, p14369_1]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [h10058, h11560, h14349, hc01, hc12, hlam, hphi, p14369_1]
                            · have p14369_0 := h14369c.1
                              have p14369_1 := h14369c.2.1
                              have p14369_2 := h14369c.2.2.1
                              have p14369_3 := h14369c.2.2.2
                              linarith only [hlam, p14369_0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h14395 | h14395
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14396 | h14396
                    · linarith only [h14350, h14396, h6793, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14398 | h14398
                      · linarith only [h11559, h11560, h14349, h14396, h14398, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14400 | h14400
                        · linarith only [h11559, h11560, h14313, h14345, h14349, h14400, h6793, hc01, hc12, hlam, hphi]
                        · linarith only [h11559, h11560, h14350, h14395, h14396, h14400, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14403 | h14403
                    · linarith only [h11558, h11560, h14349, h14403, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14405 | h14405
                      · linarith only [h11559, h11560, h14343, h14349, h14403, h14405, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14407 | h14407
                        · linarith only [h11559, h11560, h14349, h14350, h14395, h14407, h6793, hc01, hc12, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h14409 | h14409
                          · linarith only [h14350, h14395, h14409, h6793, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h14350, h14409, h6793, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14412 | h14412
                · linarith only [h14313, h14347, h14349, h14412, h6793, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h14414 | h14414
                  · linarith only [h14313, h14345, h14348, h14349, h14414, h6793, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14416 | h14416
                    · linarith only [h14412, h14416, h6793, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14418 | h14418
                      · linarith only [h11558, h14343, h14418, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14420 | h14420
                        · linarith only [h11559, h14345, h14420, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h14422 | h14422
                          · linarith only [h0, h14349, h14420, h14422, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h14412, h14422, h6793, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h11559, h14348, hlam]
          · linarith only [h0, h11558, h14347, hlam]

end R2N4
