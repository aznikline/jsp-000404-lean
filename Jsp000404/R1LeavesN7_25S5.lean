import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_25S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5718000 in
set_option maxHeartbeats 5718000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_s2 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_23_L_R_L_I_H_I_s3 m hb0 hb2 hb3 h0 h1 h2 h3
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2700 | h2700
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2701 | h2701
      · linarith only [h2, h2701, h3, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2703 | h2703
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2704 | h2704
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2705 | h2705
            · linarith only [h2, h2703, h2705, h3, hc12, hlam, hphi, ht01, u0ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2707 | h2707
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2708 | h2708
                · linarith only [h0, h2701, h2703, h2704, h2708, hc02, hlam, hphi, u0ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2710 | h2710
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2711 | h2711
                    · linarith only [h2, h2701, h2711, h3, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2713 | h2713
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2714 | h2714
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2715 | h2715
                          · rcases h2bigk with h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h2711, h3, hc12, hc34, hlam, hphi, ht23, p2716_1]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h2711, h2713, h2715, h3, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2716_1]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h3, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              rcases p2716_3 (m.d 0 2) (by simp) with h2721 | h2721
                              · rcases p2716_3 (m.d 1 2) (by simp) with h2722 | h2722
                                · linarith only [h0, h2722, hlam]
                                · linarith only [h2707, h2722, hlam]
                              · linarith only [h2721, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h0, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h0, h2713, h2715, hc01, hc45, hlam, hphi, ht0b, ht5b, p2716_1]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h2705, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              rcases p2716_3 (m.d 0 2) (by simp) with h2730 | h2730
                              · rcases p2716_3 (m.d 1 2) (by simp) with h2731 | h2731
                                · rcases p2716_3 (m.d 2 3) (by simp) with h2732 | h2732
                                  · linarith only [h2704, h2732, hlam]
                                  · linarith only [h2713, h2732, hlam]
                                · linarith only [h2731, hlam, p2716_0]
                              · linarith only [h2700, h2730, hlam]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h2, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h2704, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h2711, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h2, h2711, h3, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2716_1]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h2, h2711, hc23, hc34, hlam, hphi, p2716_1]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h2704, h2711, hc23, hc34, hlam, hphi, p2716_1]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              rcases p2716_3 (m.d 0 2) (by simp) with h2744 | h2744
                              · linarith only [h2744, h3, hlam]
                              · linarith only [h2, h2744, hlam]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              rcases p2716_3 (m.d 0 2) (by simp) with h2748 | h2748
                              · linarith only [h2748, h3, hlam]
                              · linarith only [h2700, h2748, hlam]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h2700, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h2707, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h2713, hlam, p2716_1]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h2714, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [hlam, p2716_0]
                          · linarith only [h2701, h2715, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                        · linarith only [h0, h2704, h2713, h2714, h3, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                      · linarith only [h2, h2703, h2711, h2713, h3, hc23, hc34, hlam, hphi]
                  · linarith only [h2701, h2703, h2710, hc13, hc34, hlam, hphi]
              · linarith only [h2700, h2704, h2707, h3, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h2, h2704, h3, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2762 | h2762
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2763 | h2763
            · linarith only [h0, h2763, h3, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2765 | h2765
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2766 | h2766
                · linarith only [h2701, h2766, hc13, hlam, hphi, ht01, u0ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2768 | h2768
                  · linarith only [h1, h2703, h2768, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2770 | h2770
                    · linarith only [h0, h2701, h2762, h2770, h3, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2772 | h2772
                      · linarith only [h0, h2703, h2762, h2770, h2772, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2774 | h2774
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2775 | h2775
                          · rcases h2bigk with h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c | h2776c
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [hlam, p2776_0]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h2770, h3, hc12, hc34, hlam, hphi, ht23, p2776_1]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h2770, h3, hc23, hc34, hlam, hphi, p2776_1]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h3, hlam, p2776_0]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h2770, h2772, h3, hc23, hc34, hlam, hphi, p2776_1]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h0, hlam, p2776_0]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [hlam, p2776_0]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h0, h2770, h3, hc23, hc34, hlam, hphi, p2776_1]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h2763, hlam, p2776_0]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h0, h2770, h2772, h3, hc23, hc34, hlam, hphi, p2776_1]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h2, hlam, p2776_0]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h2762, hlam, p2776_0]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [hlam, p2776_0]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h2770, hlam, p2776_0]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h2772, hlam, p2776_0]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h2770, hc34, hlam, hphi, ht01, ht12, ht23, p2776_1, u0ehi1]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h2762, h2770, hc23, hc34, hlam, hphi, p2776_1]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              rcases p2776_3 (m.d 0 2) (by simp) with h2794 | h2794
                              · linarith only [h2794, h3, hlam]
                              · linarith only [h2, h2794, hlam]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [hlam, p2776_0]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              rcases p2776_3 (m.d 0 2) (by simp) with h2798 | h2798
                              · linarith only [h2798, h3, hlam]
                              · linarith only [h2700, h2798, hlam]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h2700, hlam, p2776_0]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h2765, hlam, p2776_0]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h2700, h2770, h3, hc23, hc34, hlam, hphi, p2776_1]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [h2774, hlam, p2776_0]
                            · have p2776_0 := h2776c.1
                              have p2776_1 := h2776c.2.1
                              have p2776_2 := h2776c.2.2.1
                              have p2776_3 := h2776c.2.2.2
                              linarith only [hlam, p2776_0]
                          · linarith only [h2763, h2765, h2770, h2774, h2775, h3, hc14, hlam, hphi, ht01, u0ehi1]
                        · linarith only [h2700, h2703, h2774, h3, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
              · linarith only [h2700, h2765, h3, hc12, hc24, hlam, hphi]
          · linarith only [h2, h2762, h3, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2810 | h2810
      · linarith only [h2, h2810, h3, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2812 | h2812
        · linarith only [h2, h2700, h2812, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2814 | h2814
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2815 | h2815
            · linarith only [h2815, h3, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2817 | h2817
              · linarith only [h0, h2700, h2817, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2819 | h2819
                · linarith only [h2810, h2819, hc13, hlam, hphi, ht01, u0ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2821 | h2821
                  · linarith only [h1, h2812, h2821, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2823 | h2823
                    · linarith only [h2810, h2823, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2825 | h2825
                      · linarith only [h0, h2812, h2814, h2825, hc02, hlam, hphi, u0ehi2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2827 | h2827
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2828 | h2828
                          · rcases h2bigk with h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c | h2829c
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [hlam, p2829_0]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h2700, h2823, h2827, hc12, hc34, hlam, hphi, ht23, p2829_1]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h2700, h2823, h2827, hc23, hc34, hlam, hphi, p2829_1]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h3, hlam, p2829_0]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h2700, hlam, p2829_0]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h0, hlam, p2829_0]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [hlam, p2829_0]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h0, h2700, h2823, h2827, hc23, hc34, hlam, hphi, p2829_1]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h2815, hlam, p2829_0]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h2817, hlam, p2829_0]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h2, hlam, p2829_0]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h2814, hlam, p2829_0]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [hlam, p2829_0]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h2823, hlam, p2829_0]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h2825, hlam, p2829_0]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h2823, hc34, hlam, hphi, ht01, ht12, ht23, p2829_1, u0ehi1]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h2814, h2823, hc23, hc34, hlam, hphi, p2829_1]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              rcases p2829_3 (m.d 0 2) (by simp) with h2847 | h2847
                              · linarith only [h2847, h3, hlam]
                              · linarith only [h2, h2847, hlam]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [hlam, p2829_0]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h2, h2700, h2823, hc34, hlam, hphi, ht01, ht12, ht23, p2829_1, u0ehi2]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h2, hc25, hlam, hphi, ht01, ht12, p2829_1, u0ehi2]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h2814, h2825, hc23, hc35, hlam, hphi, p2829_1]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              rcases p2829_3 (m.d 0 2) (by simp) with h2854 | h2854
                              · linarith only [h2700, h2854, hlam]
                              · linarith only [h2, h2854, hlam]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [h2827, hlam, p2829_0]
                            · have p2829_0 := h2829c.1
                              have p2829_1 := h2829c.2.1
                              have p2829_2 := h2829c.2.2.1
                              have p2829_3 := h2829c.2.2.2
                              linarith only [hlam, p2829_0]
                          · linarith only [h2823, h2827, h2828, hlam]
                        · linarith only [h2, h2827, h3, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
          · linarith only [h2, h2814, h3, hc12, hc24, hlam, hphi]

end R2N4
