import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_43S6
import Jsp000404.R1LeavesN7_43S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1_x1_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1556 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1746 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1853 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1854 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1855 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h2669 | h2669
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2670 | h2670
    · linarith only [h1854, h1855, h2670, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2672 | h2672
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2673 | h2673
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2674 | h2674
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2675 | h2675
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2676 | h2676
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2677 | h2677
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2678 | h2678
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2679 | h2679
                    · linarith only [h1556, h1853, h1854, h2670, h2675, h2679, hc02, hc25, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2681 | h2681
                      · linarith only [h1854, h1855, h2676, h2679, h2681, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h2681, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h2678, hc14, hlam, hphi, ht45, u5elo4]
                · linarith only [h2677, hc13, hlam, hphi, ht34, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2686 | h2686
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2687 | h2687
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2688 | h2688
                    · linarith only [h1556, h1853, h2675, h2676, h2688, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2690 | h2690
                      · linarith only [h1854, h1855, h2674, h2690, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h2690, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h1855, h2674, h2687, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h1556, h1853, h2675, h2686, hc25, hlam, hphi, u5elo3]
            · linarith only [h2675, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2696 | h2696
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2697 | h2697
              · linarith only [h1556, h1853, h2670, h2673, h2674, h2696, h2697, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2699 | h2699
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2700 | h2700
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2701 | h2701
                    · linarith only [h0, h1854, h2674, h2697, h2701, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2703 | h2703
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2704 | h2704
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2705 | h2705
                          · rcases h1bigk with h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [hlam, p2706_0]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [h0, hlam, p2706_0]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [h1556, hlam, p2706_0]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [h1746, hlam, p2706_0]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [h0, h2674, h2696, h2701, h2703, h2705, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2706_1]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [h2674, h2701, hc01, hc34, hlam, hphi, ht12, ht23, p2706_1]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [hlam, p2706_0]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [h1556, h1853, h2674, h2696, h2701, h2703, h2705, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2706_1]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [h2674, hlam, p2706_1]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              rcases p2706_3 (m.d 0 1) (by simp) with h2716 | h2716
                              · linarith only [h0, h2716, hlam]
                              · linarith only [h1853, h2716, hlam]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [h1853, h2673, h2674, h2696, h2701, h2703, h2705, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2706_1]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [h2673, hlam, p2706_0]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [hlam, p2706_0]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [h2697, hlam, p2706_0]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              rcases p2706_3 (m.d 0 1) (by simp) with h2723 | h2723
                              · linarith only [h1556, h2723, hlam]
                              · linarith only [h1853, h2723, hlam]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              rcases p2706_3 (m.d 0 1) (by simp) with h2726 | h2726
                              · linarith only [h2726, hlam, p2706_0]
                              · rcases p2706_3 (m.d 1 2) (by simp) with h2728 | h2728
                                · linarith only [h2674, h2728, hlam]
                                · linarith only [h0, h2728, hlam]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [h0, h1854, h2674, h2701, hc23, hc34, hlam, hphi, p2706_1]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [h1556, h1853, h2674, h2696, h2701, h2703, h2705, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2706_1]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [hlam, p2706_0]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              rcases p2706_3 (m.d 0 1) (by simp) with h2734 | h2734
                              · linarith only [h1746, h2734, hlam]
                              · linarith only [h1853, h2734, hlam]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [h1853, hlam, p2706_0]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [h2696, hlam, p2706_0]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [h2699, hlam, p2706_0]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [h2700, hlam, p2706_0]
                            · have p2706_0 := h2706c.1
                              have p2706_1 := h2706c.2.1
                              have p2706_2 := h2706c.2.2.1
                              have p2706_3 := h2706c.2.2.2
                              linarith only [hlam, p2706_0]
                          · linarith only [h2701, h2705, hc24, hlam, hphi, ht45, u5elo4]
                        · linarith only [h1556, h1853, h2673, h2674, h2700, h2704, hlam]
                      · linarith only [h2703, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h2700, hc14, hlam, hphi, ht45, u5elo4]
                · linarith only [h1556, h1853, h2696, h2699, hc25, hlam, hphi, u5elo3]
            · linarith only [h1556, h2673, h2696, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h1853, h1854, h2673, hc02, hc15, hlam, hphi, ht0b, ht5b]
      · linarith only [h2672, hc04, hlam, hphi, ht45, u5elo4]
  · linarith only [h2669, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]

set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1556 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1746 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1853 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1854 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1855 | h1855
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1_x1_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1556 h1746 h1853 h1854 h1855
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1_x1_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1556 h1746 h1853 h1854 h1855

set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1556 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1746 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1853 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1854 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2751 | h2751
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2752 | h2752
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2753 | h2753
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2754 | h2754
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2755 | h2755
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2756 | h2756
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2757 | h2757
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2758 | h2758
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2759 | h2759
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2760 | h2760
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2761 | h2761
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2762 | h2762
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2763 | h2763
                          · linarith only [h1854, h2751, h2755, h2763, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h2763, hc24, hlam, hphi, ht45, u5elo4]
                        · linarith only [h1746, h1854, h2751, h2762, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h1746, h1853, h1854, h2751, h2753, h2761, hc03, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h2760, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h2759, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h1854, h2751, h2753, h2755, h2758, hlam]
              · linarith only [h1746, h1854, h2751, h2755, h2757, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h1854, h2751, h2755, h2756, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2773 | h2773
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2774 | h2774
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2775 | h2775
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2776 | h2776
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2777 | h2777
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2778 | h2778
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2779 | h2779
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2780 | h2780
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2781 | h2781
                            · rcases h1bigk with h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c | h2782c
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h0, hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h1556, hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h1746, hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h1746, h2755, h2773, h2774, h2779, h2781, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2755, hc01, hc23, hlam, hphi, ht12, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2755, hlam, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h1746, h2755, hc01, hc23, hlam, hphi, ht12, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                rcases p2782_3 (m.d 0 1) (by simp) with h2792 | h2792
                                · linarith only [h0, h2792, hlam]
                                · linarith only [h1853, h2792, hlam]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                rcases p2782_3 (m.d 0 1) (by simp) with h2795 | h2795
                                · linarith only [h2795, hlam, p2782_0]
                                · rcases p2782_3 (m.d 1 2) (by simp) with h2797 | h2797
                                  · linarith only [h2755, h2797, hlam]
                                  · linarith only [h0, h2797, hlam]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h0, h1853, h2755, h2774, h2779, h2781, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h1746, h1853, h2755, h2774, h2779, h2781, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                rcases p2782_3 (m.d 0 1) (by simp) with h2803 | h2803
                                · linarith only [h1556, h2803, hlam]
                                · linarith only [h1853, h2803, hlam]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h1853, h2755, h2773, h2774, h2779, h2781, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2773, hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2775, hlam, p2782_1]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                rcases p2782_3 (m.d 0 1) (by simp) with h2810 | h2810
                                · linarith only [h1746, h2810, hlam]
                                · linarith only [h1853, h2810, hlam]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h1853, hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2774, hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2776, hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [h2777, hlam, p2782_0]
                              · have p2782_0 := h2782c.1
                                have p2782_1 := h2782c.2.1
                                have p2782_2 := h2782c.2.2.1
                                have p2782_3 := h2782c.2.2.2
                                linarith only [hlam, p2782_0]
                            · linarith only [h2781, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h2777, h2780, hc24, hlam, hphi, ht45, u5elo1]
                        · linarith only [h1746, h2755, h2773, h2779, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1746, h1853, h2755, h2773, h2777, h2778, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h1746, h1853, h2774, h2777, hc25, hlam, hphi, u5elo4]
                  · linarith only [h1556, h2776, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h1556, h2753, h2775, hlam]
              · linarith only [h1746, h1853, h2773, h2774, hc15, hlam, hphi, u5elo2]
            · linarith only [h0, h2751, h2773, hlam]
        · linarith only [h2754, hc04, hlam, hphi, ht45, u5elo4]
      · linarith only [h1854, h2751, h2753, hlam]
    · linarith only [h2752, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2830 | h2830
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2831 | h2831
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2832 | h2832
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2833 | h2833
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2834 | h2834
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2835 | h2835
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2836 | h2836
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2837 | h2837
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2838 | h2838
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2839 | h2839
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2840 | h2840
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2841 | h2841
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2842 | h2842
                            · rcases h1bigk with h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c | h2843c
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [hlam, p2843_0]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [h0, hlam, p2843_0]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [h1556, hlam, p2843_0]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [h1746, hlam, p2843_0]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [h0, h2751, h2833, h2835, h2839, h2840, h2842, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2843_1]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                rcases p2843_3 (m.d 0 1) (by simp) with h2849 | h2849
                                · linarith only [h2849, hlam, p2843_0]
                                · rcases p2843_3 (m.d 1 2) (by simp) with h2851 | h2851
                                  · rcases p2843_3 (m.d 1 3) (by simp) with h2852 | h2852
                                    · linarith only [h2833, h2852, hlam]
                                    · linarith only [h1556, h2852, hlam]
                                  · linarith only [h2851, hlam, p2843_0]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [hlam, p2843_0]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [h0, h2751, h2834, h2836, hc01, hc12, hlam, hphi, p2843_1]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [h0, h1853, h2751, h2834, h2835, h2840, h2842, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2843_1]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [h0, h1853, h1854, h2833, hlam, p2843_2]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                rcases p2843_3 (m.d 0 1) (by simp) with h2860 | h2860
                                · linarith only [h2860, hlam, p2843_0]
                                · rcases p2843_3 (m.d 1 2) (by simp) with h2862 | h2862
                                  · rcases p2843_3 (m.d 1 3) (by simp) with h2863 | h2863
                                    · rcases p2843_3 (m.d 1 4) (by simp) with h2864 | h2864
                                      · linarith only [h2836, h2864, hlam]
                                      · linarith only [h1746, h2864, hlam]
                                    · linarith only [h2863, hlam, p2843_0]
                                  · linarith only [h0, h2862, hlam]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [h2833, hlam, p2843_0]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [hlam, p2843_0]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [h0, h1853, h2751, h2834, h2835, h2840, h2842, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2843_1]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                rcases p2843_3 (m.d 0 1) (by simp) with h2872 | h2872
                                · linarith only [h1556, h2872, hlam]
                                · linarith only [h1853, h2872, hlam]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                rcases p2843_3 (m.d 0 1) (by simp) with h2875 | h2875
                                · linarith only [h2875, hlam, p2843_0]
                                · rcases p2843_3 (m.d 1 2) (by simp) with h2877 | h2877
                                  · rcases p2843_3 (m.d 1 3) (by simp) with h2878 | h2878
                                    · rcases p2843_3 (m.d 1 4) (by simp) with h2879 | h2879
                                      · rcases p2843_3 (m.d 1 5) (by simp) with h2880 | h2880
                                        · linarith only [h2838, h2880, hlam]
                                        · rcases h2bigk with h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c | h2882c
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [hlam, p2882_0]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [h0, hlam, p2882_0]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [h1854, hlam, p2882_0]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [h2751, hlam, p2882_0]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [h2751, h2833, h2839, h2840, h2842, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2882_1]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            rcases p2882_3 (m.d 0 2) (by simp) with h2888 | h2888
                                            · linarith only [h0, h2888, hlam]
                                            · rcases p2882_3 (m.d 1 2) (by simp) with h2890 | h2890
                                              · rcases p2882_3 (m.d 2 3) (by simp) with h2891 | h2891
                                                · linarith only [h2833, h2891, hlam]
                                                · linarith only [h1854, h2891, hlam]
                                              · linarith only [h0, h2890, hlam]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [hlam, p2882_0]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [h0, h1853, h2751, h2835, h2839, h2840, h2842, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2882_1]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [h0, h1853, h2751, h2835, h2840, h2842, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2882_1]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [h0, h1853, h2751, h2833, h2835, h2839, hlam, p2882_2]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [h0, h1853, h2833, h2835, h2840, h2842, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2882_1]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [h2833, hlam, p2882_0]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [hlam, p2882_0]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [h0, h1853, h2751, h2833, h2835, h2840, h2842, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2882_1]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            rcases p2882_3 (m.d 0 2) (by simp) with h2903 | h2903
                                            · linarith only [h1854, h2903, hlam]
                                            · linarith only [h2830, h2903, hlam]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [h0, h1853, h2834, h2835, h2840, h2842, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2882_1]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [h2834, hlam, p2882_0]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [h2839, hlam, p2882_0]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [hlam, p2882_0]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            rcases p2882_3 (m.d 0 2) (by simp) with h2910 | h2910
                                            · linarith only [h2751, h2910, hlam]
                                            · linarith only [h2830, h2910, hlam]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [h2830, hlam, p2882_0]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [h2835, hlam, p2882_0]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [h2840, hlam, p2882_0]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [h2841, hlam, p2882_1]
                                          · have p2882_0 := h2882c.1
                                            have p2882_1 := h2882c.2.1
                                            have p2882_2 := h2882c.2.2.1
                                            have p2882_3 := h2882c.2.2.2
                                            linarith only [hlam, p2882_0]
                                      · linarith only [h2879, hlam, p2843_0]
                                    · linarith only [h1556, h2878, hlam]
                                  · linarith only [h0, h2877, hlam]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [h2834, hlam, p2843_0]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [h2836, hlam, p2843_1]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [hlam, p2843_0]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                rcases p2843_3 (m.d 0 1) (by simp) with h2924 | h2924
                                · linarith only [h1746, h2924, hlam]
                                · linarith only [h1853, h2924, hlam]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [h1853, hlam, p2843_0]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [h2835, hlam, p2843_0]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [h2837, hlam, p2843_0]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [h2838, hlam, p2843_0]
                              · have p2843_0 := h2843c.1
                                have p2843_1 := h2843c.2.1
                                have p2843_2 := h2843c.2.2.1
                                have p2843_3 := h2843c.2.2.2
                                linarith only [hlam, p2843_0]
                            · linarith only [h2842, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h2838, h2841, hc24, hlam, hphi, ht45, u5elo1]
                        · linarith only [h0, h2751, h2839, h2840, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h1853, h1854, h2831, h2838, h2839, hc03, hc45, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h1853, h2751, h2834, h2837, h2838, hc35, hlam, hphi, u5elo4]
                  · linarith only [h2837, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h1854, h2831, h2833, h2836, hlam]
              · linarith only [h0, h1854, h2833, h2835, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h1853, h1854, h2833, h2834, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2941 | h2941
            · linarith only [h0, h1853, h2751, h2833, h2941, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2943 | h2943
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2944 | h2944
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2945 | h2945
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2946 | h2946
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2947 | h2947
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2948 | h2948
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2949 | h2949
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2950 | h2950
                            · rcases h1bigk with h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c | h2951c
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [hlam, p2951_0]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [h0, hlam, p2951_0]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [h1556, hlam, p2951_0]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [h1746, hlam, p2951_0]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [h0, h2941, h2943, h2947, h2948, h2950, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2951_1]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [h2941, h2947, hc01, hc23, hlam, hphi, ht12, p2951_1]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [hlam, p2951_0]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [h2833, hlam, p2951_1]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [h2941, hlam, p2951_1]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                rcases p2951_3 (m.d 0 1) (by simp) with h2961 | h2961
                                · linarith only [h0, h2961, hlam]
                                · linarith only [h1853, h2961, hlam]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                rcases p2951_3 (m.d 0 1) (by simp) with h2964 | h2964
                                · linarith only [h2964, hlam, p2951_0]
                                · rcases p2951_3 (m.d 1 2) (by simp) with h2966 | h2966
                                  · linarith only [h2833, h2966, hlam]
                                  · linarith only [h0, h2966, hlam]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [h0, h1853, h2833, h2943, h2948, h2950, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2951_1]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [hlam, p2951_0]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [h0, h1853, h2833, h2941, h2943, h2948, h2950, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2951_1]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                rcases p2951_3 (m.d 0 1) (by simp) with h2972 | h2972
                                · linarith only [h1556, h2972, hlam]
                                · linarith only [h1853, h2972, hlam]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                rcases p2951_3 (m.d 0 1) (by simp) with h2975 | h2975
                                · linarith only [h2975, hlam, p2951_0]
                                · rcases p2951_3 (m.d 1 2) (by simp) with h2977 | h2977
                                  · linarith only [h2941, h2977, hlam]
                                  · linarith only [h0, h2977, hlam]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [h0, h1853, h2943, h2944, h2948, h2950, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2951_1]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [h2944, hlam, p2951_1]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [hlam, p2951_0]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                rcases p2951_3 (m.d 0 1) (by simp) with h2983 | h2983
                                · linarith only [h1746, h2983, hlam]
                                · linarith only [h1853, h2983, hlam]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [h1853, hlam, p2951_0]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [h2943, hlam, p2951_0]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [h2945, hlam, p2951_0]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [h2946, hlam, p2951_0]
                              · have p2951_0 := h2951c.1
                                have p2951_1 := h2951c.2.1
                                have p2951_2 := h2951c.2.2.1
                                have p2951_3 := h2951c.2.2.2
                                linarith only [hlam, p2951_0]
                            · linarith only [h2950, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1853, h2941, h2946, h2949, hlam]
                        · linarith only [h0, h2941, h2947, h2948, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1556, h2831, h2833, h2947, hlam]
                    · linarith only [h0, h2941, h2946, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h0, h1853, h2941, h2943, h2944, h2945, hc25, hlam, hphi, u5elo3]
                · linarith only [h1556, h1853, h2831, h2943, h2944, hc03, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h1853, h2943, hc15, hlam, hphi, u5elo2]
        · linarith only [h2832, hc04, hlam, hphi, ht45, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3000 | h3000
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3001 | h3001
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3002 | h3002
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3003 | h3003
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3004 | h3004
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3005 | h3005
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3006 | h3006
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3007 | h3007
                      · linarith only [h0, h1853, h1854, h2831, h3001, h3003, h3007, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h1853, h1854, h3001, h3003, h3004, h3007, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h3006, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h3005, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3012 | h3012
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3013 | h3013
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3014 | h3014
                      · linarith only [h3001, h3004, h3014, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3016 | h3016
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3017 | h3017
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3018 | h3018
                            · rcases h1bigk with h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c | h3019c
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [hlam, p3019_0]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [h0, hlam, p3019_0]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [h1556, hlam, p3019_0]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [h1746, hlam, p3019_0]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [h0, h1854, h3001, h3003, h3004, h3016, h3018, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3019_1]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                rcases p3019_3 (m.d 0 1) (by simp) with h3025 | h3025
                                · linarith only [h3025, hlam, p3019_0]
                                · rcases p3019_3 (m.d 1 2) (by simp) with h3027 | h3027
                                  · rcases p3019_3 (m.d 1 3) (by simp) with h3028 | h3028
                                    · linarith only [h3001, h3028, hlam]
                                    · linarith only [h1556, h3028, hlam]
                                  · linarith only [h3027, hlam, p3019_0]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [hlam, p3019_0]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [h0, h1854, h3001, hc01, hc12, hlam, hphi, p3019_1]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [h0, h1853, h1854, h3002, h3003, h3014, h3016, h3018, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3019_1]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [h0, h1853, h1854, h3001, hlam, p3019_2]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [h1853, h3003, h3004, h3016, h3018, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3019_1]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [h3001, hlam, p3019_0]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [hlam, p3019_0]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [h3004, hlam, p3019_0]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                rcases p3019_3 (m.d 0 1) (by simp) with h3040 | h3040
                                · linarith only [h1556, h3040, hlam]
                                · linarith only [h1853, h3040, hlam]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                rcases p3019_3 (m.d 0 1) (by simp) with h3043 | h3043
                                · linarith only [h3043, hlam, p3019_0]
                                · rcases p3019_3 (m.d 1 2) (by simp) with h3045 | h3045
                                  · rcases p3019_3 (m.d 1 3) (by simp) with h3046 | h3046
                                    · linarith only [h3004, h3046, hlam]
                                    · linarith only [h1556, h3046, hlam]
                                  · linarith only [h0, h3045, hlam]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [h3002, hlam, p3019_0]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [h1556, h1853, h3003, h3016, h3018, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p3019_1]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [hlam, p3019_0]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                rcases p3019_3 (m.d 0 1) (by simp) with h3053 | h3053
                                · linarith only [h1746, h3053, hlam]
                                · linarith only [h1853, h3053, hlam]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [h1853, hlam, p3019_0]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [h3003, hlam, p3019_0]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [h3012, hlam, p3019_0]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [h3013, hlam, p3019_0]
                              · have p3019_0 := h3019c.1
                                have p3019_1 := h3019c.2.1
                                have p3019_2 := h3019c.2.2.1
                                have p3019_3 := h3019c.2.2.2
                                linarith only [hlam, p3019_0]
                            · linarith only [h3018, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1853, h1854, h3013, h3014, h3017, hlam]
                        · linarith only [h0, h1854, h3016, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h3013, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h0, h1854, h3001, h3012, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h3003, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h1854, h3001, h3002, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3068 | h3068
            · linarith only [h0, h1853, h2751, h3001, h3068, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3070 | h3070
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3071 | h3071
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3072 | h3072
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3073 | h3073
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3074 | h3074
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3075 | h3075
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3076 | h3076
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3077 | h3077
                            · rcases h1bigk with h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c | h3078c
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [hlam, p3078_0]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [h0, hlam, p3078_0]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [h1556, hlam, p3078_0]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [h1746, hlam, p3078_0]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [h0, h1854, h2831, h3070, h3071, h3075, h3077, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p3078_1]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [h3068, h3074, hc01, hc23, hlam, hphi, ht12, p3078_1]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [hlam, p3078_0]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [h3001, hlam, p3078_1]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [h3068, hlam, p3078_1]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                rcases p3078_3 (m.d 0 1) (by simp) with h3088 | h3088
                                · linarith only [h0, h3088, hlam]
                                · linarith only [h1853, h3088, hlam]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                rcases p3078_3 (m.d 0 1) (by simp) with h3091 | h3091
                                · linarith only [h3091, hlam, p3078_0]
                                · rcases p3078_3 (m.d 1 2) (by simp) with h3093 | h3093
                                  · linarith only [h3001, h3093, hlam]
                                  · linarith only [h0, h3093, hlam]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [h0, h1853, h3001, h3070, h3075, h3077, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3078_1]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [hlam, p3078_0]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [h0, h1853, h3001, h3068, h3070, h3075, h3077, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3078_1]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [h0, h1853, h1854, h2831, h3071, hlam, p3078_2]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                rcases p3078_3 (m.d 0 1) (by simp) with h3100 | h3100
                                · linarith only [h3100, hlam, p3078_0]
                                · rcases p3078_3 (m.d 1 2) (by simp) with h3102 | h3102
                                  · linarith only [h3068, h3102, hlam]
                                  · linarith only [h0, h3102, hlam]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p3078_1]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [h3071, hlam, p3078_1]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [hlam, p3078_0]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                rcases p3078_3 (m.d 0 1) (by simp) with h3108 | h3108
                                · linarith only [h1746, h3108, hlam]
                                · linarith only [h1853, h3108, hlam]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [h1853, hlam, p3078_0]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [h3070, hlam, p3078_0]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [h3072, hlam, p3078_0]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [h3073, hlam, p3078_0]
                              · have p3078_0 := h3078c.1
                                have p3078_1 := h3078c.2.1
                                have p3078_2 := h3078c.2.2.1
                                have p3078_3 := h3078c.2.2.2
                                linarith only [hlam, p3078_0]
                            · linarith only [h1854, h2831, h3077, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h0, h1853, h3068, h3073, h3076, hlam]
                        · linarith only [h0, h1854, h2831, h3001, h3071, h3075, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h3001, h3071, h3074, hlam]
                    · linarith only [h3073, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h0, h1853, h1854, h2831, h3070, h3071, h3072, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3122 | h3122
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3123 | h3123
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3124 | h3124
                      · linarith only [h1556, h1853, h3070, h3071, h3124, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h1853, h3001, h3070, h3124, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h1853, h3001, h3070, h3071, h3123, hc25, hlam, hphi, u5elo4]
                  · linarith only [h0, h1853, h3001, h3070, h3122, hc25, hlam, hphi, u5elo3]
              · linarith only [h0, h3070, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h1853, h1854, h2831, h3000, hc15, hlam, hphi, u5elo4]
    · linarith only [h0, h1853, h2830, hc15, hlam, hphi, u5elo2]

set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1556 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1746 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1853 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1854 | h1854
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1_x1_x0_x0 m hb1 hb2 hb4 hb5 h0 h1556 h1746 h1853 h1854
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1_x1_x0_x1 m hb1 hb2 hb4 hb5 h0 h1556 h1746 h1853 h1854

set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1556 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1746 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1853 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [h1853, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1556 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1746 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1853 | h1853
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 h0 h1556 h1746 h1853
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 h0 h1556 h1746 h1853

set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1556 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1746 | h1746
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1_x0 m hb1 hb2 hb4 hb5 h0 h1556 h1746
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1_x1 m hb1 hb2 hb4 hb5 h0 h1556 h1746

set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1556 | h1556
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x0 m hb1 hb2 hb4 hb5 h0 h1556
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1 m hb1 hb2 hb4 hb5 h0 h1556

set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0 m hb1 hb2 hb4 hb5 h0
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1 m hb1 hb2 hb4 hb5 h0

end R2N4
