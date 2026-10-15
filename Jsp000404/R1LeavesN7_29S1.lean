import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_29S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6334000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1951 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1952 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h2662 | h2662
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2663 | h2663
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2664 | h2664
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2665 | h2665
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2666 | h2666
          · linarith only [h1951, h1952, h2666, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2668 | h2668
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2669 | h2669
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2670 | h2670
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2671 | h2671
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2672 | h2672
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2673 | h2673
                      · linarith only [h1951, h2666, h2673, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2675 | h2675
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2676 | h2676
                          · linarith only [h1951, h1952, h2670, h2673, h2676, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2678 | h2678
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2679 | h2679
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2680 | h2680
                                · rcases h0bigk with h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c | h2681c
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [hlam, p2681_0]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [h0, hlam, p2681_1]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [h1952, h2673, hc03, hc34, hlam, hphi, p2681_1]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [h1952, hlam, p2681_1]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    rcases p2681_3 (m.d 0 1) (by simp) with h2686 | h2686
                                    · rcases p2681_3 (m.d 0 2) (by simp) with h2687 | h2687
                                      · rcases p2681_3 (m.d 0 3) (by simp) with h2688 | h2688
                                        · linarith only [h1951, h2688, hlam]
                                        · linarith only [h2668, h2688, hlam]
                                      · linarith only [h2665, h2687, hlam]
                                    · linarith only [h2662, h2686, hlam]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [h1951, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2681_1, u0elo1]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [hlam, p2681_0]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [h2668, h2680, hc45, hlam, hphi, ht0b, ht5b, p2681_1, u0elo1]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [h1951, h1952, h2670, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2681_1, u0elo1]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    rcases p2681_3 (m.d 0 1) (by simp) with h2697 | h2697
                                    · linarith only [h0, h2697, hlam]
                                    · linarith only [h2662, h2697, hlam]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [h1951, hlam, p2681_1]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [h2663, hlam, p2681_1]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [hlam, p2681_0]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [h2666, hlam, p2681_1]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    rcases p2681_3 (m.d 0 1) (by simp) with h2704 | h2704
                                    · rcases p2681_3 (m.d 0 2) (by simp) with h2705 | h2705
                                      · rcases p2681_3 (m.d 0 3) (by simp) with h2706 | h2706
                                        · rcases p2681_3 (m.d 0 4) (by simp) with h2707 | h2707
                                          · rcases p2681_3 (m.d 0 5) (by simp) with h2708 | h2708
                                            · linarith only [h2668, h2708, hlam]
                                            · rcases h2bigk with h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c | h2710c
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [hlam, p2710_0]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [h0, hlam, p2710_1]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [h2678, h2680, hc45, hlam, hphi, ht0b, ht5b, p2710_1, u0elo1]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [h2676, h2678, h2680, hc45, hlam, hphi, ht0b, ht5b, p2710_1, u0elo1]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                rcases p2710_3 (m.d 0 2) (by simp) with h2715 | h2715
                                                · rcases p2710_3 (m.d 1 2) (by simp) with h2716 | h2716
                                                  · rcases p2710_3 (m.d 2 3) (by simp) with h2717 | h2717
                                                    · linarith only [h2663, h2717, hlam]
                                                    · linarith only [h2678, h2717, hlam]
                                                  · linarith only [h2672, h2716, hlam]
                                                · linarith only [h2715, hlam, p2710_0]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [h0, h1951, h2662, h2672, h2678, h2680, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2681_1, p2710_1]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [hlam, p2710_0]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                rcases p2710_3 (m.d 0 2) (by simp) with h2724 | h2724
                                                · linarith only [h0, h2724, hlam]
                                                · linarith only [h2663, h2724, hlam]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                rcases p2710_3 (m.d 0 2) (by simp) with h2727 | h2727
                                                · linarith only [h0, h2727, hlam]
                                                · linarith only [h2664, h2727, hlam]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [h0, h1951, h2662, h2672, hlam, p2681_1, p2710_2]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [h2663, hlam, p2710_0]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [h2670, hlam, p2710_0]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [hlam, p2710_0]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [h2676, hlam, p2710_0]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [h2663, h2678, h2680, hc45, hlam, hphi, ht0b, ht5b, p2710_1, u0elo1]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [h2664, hlam, p2710_0]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [h2671, hlam, p2710_0]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [h1951, h1952, h2662, h2664, h2672, h2673, h2678, h2680, hc23, hc34, hc45, hlam, hphi, ht0b, ht5b, p2681_1, p2710_1, u0elo1]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [hlam, p2710_0]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [h2664, h2678, h2680, hc45, hlam, hphi, ht0b, ht5b, p2710_1, u0elo1]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [h2665, hlam, p2710_0]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [h2672, hlam, p2710_0]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [h2678, hlam, p2710_1]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [h2679, hlam, p2710_0]
                                              · have p2710_0 := h2710c.1
                                                have p2710_1 := h2710c.2.1
                                                have p2710_2 := h2710c.2.2.1
                                                have p2710_3 := h2710c.2.2.2
                                                linarith only [hlam, p2710_0]
                                          · linarith only [h2669, h2707, hlam]
                                        · linarith only [h2668, h2706, hlam]
                                      · linarith only [h2665, h2705, hlam]
                                    · linarith only [h2662, h2704, hlam]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [h1951, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2681_1, u0elo3]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [h2664, hlam, p2681_0]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [h2663, h2678, h2680, hc45, hlam, hphi, ht0b, ht5b, p2681_1, u0elo3]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [hlam, p2681_0]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    rcases p2681_3 (m.d 0 1) (by simp) with h2754 | h2754
                                    · linarith only [h1952, h2754, hlam]
                                    · linarith only [h2662, h2754, hlam]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [h2662, hlam, p2681_0]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [h2665, hlam, p2681_1]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [h2668, hlam, p2681_0]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [h2669, hlam, p2681_1]
                                  · have p2681_0 := h2681c.1
                                    have p2681_1 := h2681c.2.1
                                    have p2681_2 := h2681c.2.2.1
                                    have p2681_3 := h2681c.2.2.2
                                    linarith only [hlam, p2681_0]
                                · linarith only [h1951, h1952, h2673, h2680, hc13, hc45, hlam, hphi, ht34]
                              · linarith only [h2669, h2676, h2678, h2679, hc35, hlam, hphi, u5elo0]
                            · linarith only [h1951, h1952, h2668, h2673, h2678, hc23, hc34, hlam, hphi]
                        · linarith only [h1951, h1952, h2668, h2673, h2675, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h2672, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h2664, h2671, hlam]
                · linarith only [h0, h2663, h2670, hlam]
              · linarith only [h1951, h1952, h2669, hc13, hlam, hphi, ht34, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2770 | h2770
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2771 | h2771
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2772 | h2772
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2773 | h2773
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2774 | h2774
                      · linarith only [h1951, h2668, h2774, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2776 | h2776
                        · linarith only [h1951, h2668, h2776, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2778 | h2778
                          · linarith only [h1951, h1952, h2662, h2771, h2774, h2778, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2780 | h2780
                            · linarith only [h1951, h2668, h2771, h2780, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2782 | h2782
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2783 | h2783
                                · rcases h0bigk with h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c | h2784c
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [hlam, p2784_0]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [h0, hlam, p2784_1]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [h1951, h1952, h2771, h2774, hc23, hc34, hlam, hphi, p2784_1]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [h1952, hlam, p2784_1]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [h1951, h1952, h2668, h2771, h2774, hc23, hc34, hlam, hphi, p2784_1]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [h1951, h2771, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2784_1, u0elo1]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [hlam, p2784_0]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    rcases p2784_3 (m.d 0 1) (by simp) with h2792 | h2792
                                    · linarith only [h0, h2792, hlam]
                                    · linarith only [h1951, h2792, hlam]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [h1952, h2662, h2771, h2776, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2784_1, u0elo1]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    rcases p2784_3 (m.d 0 1) (by simp) with h2796 | h2796
                                    · linarith only [h0, h2796, hlam]
                                    · linarith only [h2662, h2796, hlam]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [h1951, hlam, p2784_1]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [h2663, hlam, p2784_1]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [hlam, p2784_0]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [h2666, hlam, p2784_1]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [h2668, hlam, p2784_1]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [h2662, h2771, h2776, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2784_1, u0elo3]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [h2664, hlam, p2784_0]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    rcases p2784_3 (m.d 0 1) (by simp) with h2806 | h2806
                                    · linarith only [h1952, h2806, hlam]
                                    · linarith only [h1951, h2806, hlam]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [hlam, p2784_0]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    rcases p2784_3 (m.d 0 1) (by simp) with h2810 | h2810
                                    · linarith only [h1952, h2810, hlam]
                                    · linarith only [h2662, h2810, hlam]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [h2662, hlam, p2784_0]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [h2665, hlam, p2784_1]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [h1951, h2771, hc23, hlam, hphi, ht34, ht45, p2784_1, u5elo0]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [h2770, hlam, p2784_1]
                                  · have p2784_0 := h2784c.1
                                    have p2784_1 := h2784c.2.1
                                    have p2784_2 := h2784c.2.2.1
                                    have p2784_3 := h2784c.2.2.2
                                    linarith only [hlam, p2784_0]
                                · linarith only [h1952, h2774, h2783, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2819 | h2819
                                · rcases h0bigk with h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c | h2820c
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [hlam, p2820_0]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h0, hlam, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h1951, h1952, h2774, hc13, hc34, hlam, hphi, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h1952, hlam, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2770, h2778, h2782, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2820_1, u0elo0]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2662, hc15, hlam, hphi, ht0b, ht5b, p2820_1, u0elo1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [hlam, p2820_0]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    rcases p2820_3 (m.d 0 1) (by simp) with h2828 | h2828
                                    · linarith only [h0, h2828, hlam]
                                    · linarith only [h1951, h2828, hlam]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h1952, h2662, h2770, h2778, h2782, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2820_1, u0elo1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2770, h2778, h2782, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2820_1, u0elo1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h1951, hlam, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2663, hlam, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [hlam, p2820_0]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2666, hlam, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2668, hlam, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2662, h2770, h2778, h2782, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2820_1, u0elo3]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2664, hlam, p2820_0]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    rcases p2820_3 (m.d 0 1) (by simp) with h2840 | h2840
                                    · linarith only [h1952, h2840, hlam]
                                    · linarith only [h1951, h2840, hlam]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [hlam, p2820_0]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2664, h2770, h2778, h2782, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2820_1, u0elo1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2662, hlam, p2820_0]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2665, hlam, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h1951, h2771, hc23, hlam, hphi, ht34, ht45, p2820_1, u5elo0]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [h2770, hlam, p2820_1]
                                  · have p2820_0 := h2820c.1
                                    have p2820_1 := h2820c.2.1
                                    have p2820_2 := h2820c.2.2.1
                                    have p2820_3 := h2820c.2.2.2
                                    linarith only [hlam, p2820_0]
                                · linarith only [h1951, h2666, h2771, h2819, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h1952, h2772, h2773, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h2664, h2772, hlam]
                · linarith only [h0, h2663, h2771, hlam]
              · linarith only [h1951, h1952, h2770, hc13, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h1951, h1952, h2664, h2665, hc13, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2856 | h2856
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2857 | h2857
          · linarith only [h0, h1951, h2664, h2857, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2859 | h2859
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2860 | h2860
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2861 | h2861
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2862 | h2862
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2863 | h2863
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2864 | h2864
                      · linarith only [h0, h1951, h2857, h2864, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2866 | h2866
                        · linarith only [h0, h1951, h2664, h2862, h2866, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h1951, h2664, h2859, h2861, h2862, h2866, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h2664, h2862, h2863, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2870 | h2870
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2871 | h2871
                      · linarith only [h0, h1951, h2862, h2871, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2873 | h2873
                        · linarith only [h0, h1951, h2862, h2873, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h1951, h2859, h2862, h2873, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h2870, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h1951, h2663, h2861, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h1951, h1952, h2860, hc13, hlam, hphi, ht34, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2879 | h2879
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2880 | h2880
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2881 | h2881
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2882 | h2882
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2883 | h2883
                      · linarith only [h0, h1951, h2662, h2664, h2857, h2859, h2882, h2883, hc25, hlam, hphi, u5elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2885 | h2885
                        · linarith only [h1951, h2859, h2885, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2887 | h2887
                          · linarith only [h0, h2664, h2880, h2881, h2883, h2885, h2887, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2889 | h2889
                            · linarith only [h1951, h2859, h2880, h2889, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2891 | h2891
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2892 | h2892
                                · rcases h0bigk with h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [hlam, p2893_0]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h0, hlam, p2893_1]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h0, h1951, h2664, h2880, h2881, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2893_1]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h1952, hlam, p2893_1]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h0, h2664, h2881, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2893_1]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h2664, h2881, hc01, hc12, hlam, hphi, p2893_1]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [hlam, p2893_0]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h1951, h2664, h2880, h2881, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2893_1]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h2664, hlam, p2893_1]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h2662, h2664, h2880, h2881, h2885, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2893_1]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h1951, hlam, p2893_1]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h2663, hlam, p2893_1]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [hlam, p2893_0]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h2857, hlam, p2893_1]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h2859, hlam, p2893_1]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h2662, h2880, h2885, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2893_1, u0elo3]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h0, h2662, h2664, h2880, h2881, h2885, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2893_1]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    rcases p2893_3 (m.d 0 1) (by simp) with h2911 | h2911
                                    · linarith only [h1952, h2911, hlam]
                                    · linarith only [h1951, h2911, hlam]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [hlam, p2893_0]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    rcases p2893_3 (m.d 0 1) (by simp) with h2915 | h2915
                                    · linarith only [h1952, h2915, hlam]
                                    · linarith only [h2662, h2915, hlam]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h2662, hlam, p2893_0]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h2856, hlam, p2893_1]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h1951, h2880, hc23, hlam, hphi, ht34, ht45, p2893_1, u5elo0]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [h2879, hlam, p2893_1]
                                  · have p2893_0 := h2893c.1
                                    have p2893_1 := h2893c.2.1
                                    have p2893_2 := h2893c.2.2.1
                                    have p2893_3 := h2893c.2.2.2
                                    linarith only [hlam, p2893_0]
                                · linarith only [h1952, h2662, h2880, h2883, h2885, h2892, hc23, hlam, hphi, ht34, ht45, u5elo4]
                              · linarith only [h0, h2662, h2664, h2879, h2891, hlam]
                    · linarith only [h0, h2882, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2926 | h2926
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2927 | h2927
                      · linarith only [h0, h1951, h2857, h2881, h2927, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2929 | h2929
                        · linarith only [h1951, h2859, h2929, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2931 | h2931
                          · linarith only [h0, h2662, h2880, h2881, h2927, h2929, h2931, hlam]
                          · linarith only [h0, h2662, h2880, h2881, h2929, h2931, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h2926, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h1951, h2663, h2880, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h1951, h1952, h2879, hc13, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h0, h1951, h2856, hc13, hlam, hphi, ht34, ht45, u5elo2]
    · linarith only [h0, h1951, h2663, hlam]
  · linarith only [h1951, h2662, hc13, hlam, hphi, ht34, ht45, u5elo1]

set_option maxHeartbeats 6334000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1951 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h1952 | h1952
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h1951 h1952
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h1951 h1952

set_option maxHeartbeats 6334000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1951 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2940 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h2941 | h2941
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2942 | h2942
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2943 | h2943
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2944 | h2944
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2945 | h2945
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2946 | h2946
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2947 | h2947
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2948 | h2948
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2949 | h2949
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2950 | h2950
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2951 | h2951
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2952 | h2952
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2953 | h2953
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2954 | h2954
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2955 | h2955
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2956 | h2956
                                · linarith only [h2942, h2953, h2956, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                · linarith only [h2940, h2949, h2955, h2956, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2959 | h2959
                                · linarith only [h2942, h2945, h2955, h2959, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases h0bigk with h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c | h2961c
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [hlam, p2961_0]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h0, hlam, p2961_1]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h1951, hlam, p2961_0]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h1951, h2947, h2948, h2955, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p2961_1]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h1951, h2947, h2948, h2953, h2955, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2961_1]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h2940, hc14, hlam, hphi, ht0b, ht45, ht5b, p2961_1, u0elo1]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [hlam, p2961_0]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h1951, h2940, hc14, hlam, hphi, ht0b, ht45, ht5b, p2961_1, u0elo1]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h2947, h2953, h2955, hc34, hlam, hphi, ht0b, ht45, ht5b, p2961_1, u0elo1]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h2947, h2953, h2955, hc34, hlam, hphi, ht0b, ht45, ht5b, p2961_1, u0elo1]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h2940, h2947, h2953, h2955, hc34, hlam, hphi, ht0b, ht45, ht5b, p2961_1, u0elo2]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h2942, hlam, p2961_1]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [hlam, p2961_0]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h2942, h2947, h2953, h2955, hc34, hlam, hphi, ht0b, ht45, ht5b, p2961_1, u0elo1]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h2942, h2947, h2953, h2955, hc34, hlam, hphi, ht0b, ht45, ht5b, p2961_1, u0elo1]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h2940, hlam, p2961_0]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h2943, hlam, p2961_0]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h2945, hlam, p2961_0]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [hlam, p2961_0]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h2940, h2947, h2953, h2955, hc34, hlam, hphi, ht0b, ht45, ht5b, p2961_1, u0elo0]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h2941, hlam, p2961_0]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h2944, hlam, p2961_1]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h2946, hlam, p2961_0]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [h2947, hlam, p2961_1]
                                  · have p2961_0 := h2961c.1
                                    have p2961_1 := h2961c.2.1
                                    have p2961_2 := h2961c.2.2.1
                                    have p2961_3 := h2961c.2.2.2
                                    linarith only [hlam, p2961_0]
                            · linarith only [h1951, h2941, h2948, h2952, h2953, h2954, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2988 | h2988
                            · linarith only [h1951, h2940, h2948, h2951, h2953, h2988, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2990 | h2990
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2991 | h2991
                                · rcases h0bigk with h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c | h2992c
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [hlam, p2992_0]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h0, hlam, p2992_1]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h1951, hlam, p2992_0]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h1951, h2940, h2948, h2951, h2988, h2991, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2992_1]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h1951, h2946, h2948, h2988, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2992_1]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h2940, h2951, h2988, h2991, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2992_1, u0elo1]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [hlam, p2992_0]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h1951, h2940, h2951, h2988, h2991, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2992_1, u0elo1]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h2940, h2951, h2988, h2991, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2992_1, u0elo1]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h2946, h2988, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2992_1, u0elo1]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h2940, h2951, h2988, h2991, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2992_1, u0elo2]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h2942, hlam, p2992_1]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [hlam, p2992_0]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h2940, h2942, h2951, h2988, h2991, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2992_1, u0elo1]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h2942, h2946, h2988, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2992_1, u0elo1]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h2940, hlam, p2992_0]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h2943, hlam, p2992_0]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h2945, hlam, p2992_0]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [hlam, p2992_0]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h2946, h2988, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2992_1, u0elo3]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h2941, hlam, p2992_0]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h2944, hlam, p2992_1]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h2946, hlam, p2992_0]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [h2947, hlam, p2992_1]
                                  · have p2992_0 := h2992c.1
                                    have p2992_1 := h2992c.2.1
                                    have p2992_2 := h2992c.2.2.1
                                    have p2992_3 := h2992c.2.2.2
                                    linarith only [hlam, p2992_0]
                                · linarith only [h2943, h2990, h2991, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3019 | h3019
                                · linarith only [h1951, h2940, h2948, h2951, h2953, h2990, h3019, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · linarith only [h1951, h2940, h2947, h2948, h2953, h3019, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h1951, h2952, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h1951, h2945, h2951, hlam]
                    · linarith only [h0, h2940, h2949, h2950, hc24, hlam, hphi, ht45, u5elo2]
                  · linarith only [h0, h2943, h2949, hlam]
                · linarith only [h0, h2942, h2948, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3027 | h3027
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3028 | h3028
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3029 | h3029
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3030 | h3030
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3031 | h3031
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3032 | h3032
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3033 | h3033
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3034 | h3034
                              · linarith only [h2940, h2947, h3028, h3034, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3036 | h3036
                                · linarith only [h2942, h2945, h2947, h3036, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases h0bigk with h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c | h3038c
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [hlam, p3038_0]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [h0, hlam, p3038_1]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [h1951, hlam, p3038_0]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    rcases p3038_3 (m.d 0 1) (by simp) with h3042 | h3042
                                    · rcases p3038_3 (m.d 0 2) (by simp) with h3043 | h3043
                                      · rcases p3038_3 (m.d 0 3) (by simp) with h3044 | h3044
                                        · rcases p3038_3 (m.d 0 4) (by simp) with h3045 | h3045
                                          · linarith only [h2940, h3045, hlam]
                                          · rcases p3038_3 (m.d 0 5) (by simp) with h3047 | h3047
                                            · linarith only [h2941, h3047, hlam]
                                            · linarith only [h2947, h3047, hlam]
                                        · linarith only [h2945, h3044, hlam]
                                      · linarith only [h2943, h3043, hlam]
                                    · linarith only [h2940, h3042, hlam]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    rcases p3038_3 (m.d 0 1) (by simp) with h3053 | h3053
                                    · rcases p3038_3 (m.d 0 2) (by simp) with h3054 | h3054
                                      · rcases p3038_3 (m.d 0 3) (by simp) with h3055 | h3055
                                        · rcases p3038_3 (m.d 0 4) (by simp) with h3056 | h3056
                                          · linarith only [h2940, h3056, hlam]
                                          · rcases p3038_3 (m.d 0 5) (by simp) with h3058 | h3058
                                            · linarith only [h2941, h3058, hlam]
                                            · rcases h2bigk with h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c | h3060c
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [hlam, p3060_0]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [h0, hlam, p3060_1]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [h3032, hc34, hlam, hphi, ht0b, ht45, ht5b, p3060_1, u0elo1]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                rcases p3060_3 (m.d 0 2) (by simp) with h3064 | h3064
                                                · rcases p3060_3 (m.d 1 2) (by simp) with h3065 | h3065
                                                  · rcases p3060_3 (m.d 2 3) (by simp) with h3066 | h3066
                                                    · linarith only [h2942, h3066, hlam]
                                                    · linarith only [h3032, h3066, hlam]
                                                  · linarith only [h3028, h3065, hlam]
                                                · linarith only [h3064, hlam, p3060_0]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                rcases p3060_3 (m.d 0 2) (by simp) with h3071 | h3071
                                                · rcases p3060_3 (m.d 1 2) (by simp) with h3072 | h3072
                                                  · rcases p3060_3 (m.d 2 3) (by simp) with h3073 | h3073
                                                    · linarith only [h2942, h3073, hlam]
                                                    · linarith only [h3033, h3073, hlam]
                                                  · linarith only [h3029, h3072, hlam]
                                                · linarith only [h3071, hlam, p3060_0]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3038_1, p3060_1]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [hlam, p3060_0]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                rcases p3060_3 (m.d 0 2) (by simp) with h3080 | h3080
                                                · linarith only [h0, h3080, hlam]
                                                · linarith only [h2942, h3080, hlam]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [h0, h2940, h2947, h3028, hlam, p3038_1, p3060_2]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [h1951, h2941, h3027, h3029, hlam, p3038_1, p3060_2]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [h2942, hlam, p3060_0]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [h3027, hlam, p3060_0]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [hlam, p3060_0]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [h2942, h3032, hc34, hlam, hphi, ht0b, ht45, ht5b, p3060_1, u0elo1]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [h2942, hc25, hlam, hphi, ht0b, ht5b, p3060_1, u0elo1]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [h2943, hlam, p3060_0]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [h3028, hlam, p3060_0]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [h3032, hlam, p3060_1]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [hlam, p3060_0]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [h3034, hlam, p3060_1]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [h2944, hlam, p3060_0]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [h3029, hlam, p3060_0]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [h3033, hlam, p3060_1]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [h3032, hc34, hlam, hphi, ht45, p3060_1, u5elo2]
                                              · have p3060_0 := h3060c.1
                                                have p3060_1 := h3060c.2.1
                                                have p3060_2 := h3060c.2.2.1
                                                have p3060_3 := h3060c.2.2.2
                                                linarith only [hlam, p3060_0]
                                        · linarith only [h2946, h3055, hlam]
                                      · linarith only [h2944, h3054, hlam]
                                    · linarith only [h2941, h3053, hlam]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [h2940, h3028, h3032, hc34, hlam, hphi, ht0b, ht45, ht5b, p3038_1, u0elo1]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [hlam, p3038_0]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [h1951, h2940, h3028, h3032, hc34, hlam, hphi, ht0b, ht45, ht5b, p3038_1, u0elo1]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    rcases p3038_3 (m.d 0 1) (by simp) with h3106 | h3106
                                    · linarith only [h0, h3106, hlam]
                                    · linarith only [h2940, h3106, hlam]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    rcases p3038_3 (m.d 0 1) (by simp) with h3109 | h3109
                                    · linarith only [h0, h3109, hlam]
                                    · linarith only [h2941, h3109, hlam]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [h2941, h3029, h3033, h3036, hc34, hlam, hphi, ht0b, ht45, ht5b, p3038_1, u0elo2]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [h2942, hlam, p3038_1]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [hlam, p3038_0]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    rcases p3038_3 (m.d 0 1) (by simp) with h3115 | h3115
                                    · linarith only [h1951, h3115, hlam]
                                    · linarith only [h2940, h3115, hlam]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    rcases p3038_3 (m.d 0 1) (by simp) with h3118 | h3118
                                    · linarith only [h1951, h3118, hlam]
                                    · linarith only [h2941, h3118, hlam]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [h2940, hlam, p3038_0]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [h2943, hlam, p3038_0]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [h2945, hlam, p3038_0]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [hlam, p3038_0]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [h2947, hlam, p3038_0]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [h2941, hlam, p3038_0]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [h2944, hlam, p3038_1]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [h2946, hlam, p3038_0]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [h2940, h3028, h3032, hc34, hlam, hphi, ht45, p3038_1, u5elo0]
                                  · have p3038_0 := h3038c.1
                                    have p3038_1 := h3038c.2.1
                                    have p3038_2 := h3038c.2.2.1
                                    have p3038_3 := h3038c.2.2.2
                                    linarith only [hlam, p3038_0]
                            · linarith only [h2941, h3031, h3032, h3033, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h2945, h2947, h3032, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h1951, h3031, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h1951, h2945, h3030, hlam]
                    · linarith only [h0, h3029, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h2943, h3028, hlam]
                · linarith only [h0, h2942, h3027, hlam]
            · linarith only [h1951, h2940, h2946, hc14, hlam, hphi, ht45, u5elo3]
          · linarith only [h1951, h2940, h2945, hlam]
        · linarith only [h0, h2940, h2944, hc14, hlam, hphi, ht45, u5elo2]
      · linarith only [h1951, h2940, h2942, h2943, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3142 | h3142
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3143 | h3143
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3144 | h3144
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3145 | h3145
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3146 | h3146
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3147 | h3147
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3148 | h3148
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3149 | h3149
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3150 | h3150
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3151 | h3151
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3152 | h3152
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3153 | h3153
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3154 | h3154
                              · linarith only [h0, h2940, h2942, h3147, h3148, h3154, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h0, h2940, h2942, h3146, h3147, h3152, h3154, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h2942, h3153, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · linarith only [h0, h2942, h3144, h3152, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1951, h2940, h3148, h3151, hc24, hlam, hphi, ht45, u5elo3]
                      · linarith only [h2942, h3144, h3147, h3150, hlam]
                    · linarith only [h0, h2940, h3148, h3149, hc24, hlam, hphi, ht45, u5elo2]
                  · linarith only [h0, h2940, h2942, h3147, h3148, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3163 | h3163
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3164 | h3164
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3165 | h3165
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3166 | h3166
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3167 | h3167
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3168 | h3168
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3169 | h3169
                              · linarith only [h0, h2940, h3147, h3163, h3169, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h0, h2940, h3146, h3147, h3169, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h3147, h3168, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h3147, h3167, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1951, h2940, h3163, h3166, hc24, hlam, hphi, ht45, u5elo3]
                      · linarith only [h0, h2940, h3144, h3147, h3163, h3165, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h0, h2940, h3163, h3164, hc24, hlam, hphi, ht45, u5elo2]
                  · linarith only [h0, h3142, h3163, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3178 | h3178
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3179 | h3179
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3180 | h3180
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3181 | h3181
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3182 | h3182
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3183 | h3183
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3184 | h3184
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3185 | h3185
                              · linarith only [h0, h2940, h2942, h3178, h3179, h3185, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3187 | h3187
                                · linarith only [h2942, h3144, h3146, h3178, h3187, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases h0bigk with h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c | h3189c
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [hlam, p3189_0]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h0, hlam, p3189_1]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h1951, hlam, p3189_0]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h0, h2940, h2942, h3178, h3179, h3183, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3189_1]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h0, h2942, h3178, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3189_1]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h2942, h3178, hc01, hc12, hlam, hphi, p3189_1]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [hlam, p3189_0]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h2942, hlam, p3189_0]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h2940, h2942, h3178, h3179, h3183, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3189_1]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h2941, h2942, h3178, h3180, h3184, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3189_1]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h2940, h2942, h3178, h3179, h3183, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3189_1]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h0, h2940, h2942, h3178, h3179, h3183, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3189_1]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [hlam, p3189_0]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    rcases p3189_3 (m.d 0 1) (by simp) with h3203 | h3203
                                    · linarith only [h1951, h3203, hlam]
                                    · linarith only [h2940, h3203, hlam]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    rcases p3189_3 (m.d 0 1) (by simp) with h3206 | h3206
                                    · linarith only [h1951, h3206, hlam]
                                    · linarith only [h2941, h3206, hlam]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h2940, hlam, p3189_0]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h3142, hlam, p3189_0]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h3144, hlam, p3189_0]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [hlam, p3189_0]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h3146, hlam, p3189_0]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h2941, hlam, p3189_0]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h3143, hlam, p3189_1]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h3145, hlam, p3189_0]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [h2940, h3179, h3183, hc34, hlam, hphi, ht45, p3189_1, u5elo0]
                                  · have p3189_0 := h3189c.1
                                    have p3189_1 := h3189c.2.1
                                    have p3189_2 := h3189c.2.2.1
                                    have p3189_3 := h3189c.2.2.2
                                    linarith only [hlam, p3189_0]
                            · linarith only [h1951, h2941, h2942, h3180, h3184, hc25, hlam, hphi, u5elo3]
                          · linarith only [h0, h2940, h2942, h3144, h3179, h3183, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h1951, h2940, h3179, h3182, hc24, hlam, hphi, ht45, u5elo3]
                      · linarith only [h2942, h3144, h3178, h3181, hlam]
                    · linarith only [h0, h2940, h3179, h3180, hc24, hlam, hphi, ht45, u5elo2]
                  · linarith only [h0, h2940, h2942, h3178, h3179, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3225 | h3225
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3226 | h3226
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3227 | h3227
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3228 | h3228
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3229 | h3229
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3230 | h3230
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3231 | h3231
                              · linarith only [h2940, h3146, h3225, h3231, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3233 | h3233
                                · linarith only [h3144, h3146, h3233, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                · rcases h0bigk with h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c | h3235c
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [hlam, p3235_0]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [h0, hlam, p3235_1]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [h1951, hlam, p3235_0]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [h0, h2940, h3178, h3225, h3229, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3235_1]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [h0, h3178, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3235_1]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [h2941, hc15, hlam, hphi, ht0b, ht5b, p3235_1, u0elo1]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [hlam, p3235_0]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [h2942, hlam, p3235_0]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    rcases p3235_3 (m.d 0 1) (by simp) with h3244 | h3244
                                    · linarith only [h0, h3244, hlam]
                                    · linarith only [h2940, h3244, hlam]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    rcases p3235_3 (m.d 0 1) (by simp) with h3247 | h3247
                                    · linarith only [h0, h3247, hlam]
                                    · linarith only [h2941, h3247, hlam]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [h2941, h3226, h3229, h3231, hc34, hlam, hphi, ht0b, ht45, ht5b, p3235_1, u0elo2]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [h0, h2941, h3226, h3229, h3231, hc34, hlam, hphi, ht0b, ht45, ht5b, p3235_1, u0elo2]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [hlam, p3235_0]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    rcases p3235_3 (m.d 0 1) (by simp) with h3253 | h3253
                                    · linarith only [h1951, h3253, hlam]
                                    · linarith only [h2940, h3253, hlam]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    rcases p3235_3 (m.d 0 1) (by simp) with h3256 | h3256
                                    · linarith only [h1951, h3256, hlam]
                                    · linarith only [h2941, h3256, hlam]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [h2940, hlam, p3235_0]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [h3142, hlam, p3235_0]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [h3144, hlam, p3235_0]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [hlam, p3235_0]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [h3146, hlam, p3235_0]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [h2941, hlam, p3235_0]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [h3143, hlam, p3235_1]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [h3145, hlam, p3235_0]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [h2940, h3225, h3229, hc34, hlam, hphi, ht45, p3235_1, u5elo0]
                                  · have p3235_0 := h3235c.1
                                    have p3235_1 := h3235c.2.1
                                    have p3235_2 := h3235c.2.2.1
                                    have p3235_3 := h3235c.2.2.2
                                    linarith only [hlam, p3235_0]
                            · linarith only [h3178, h3230, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                          · linarith only [h0, h3178, h3229, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1951, h3228, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h1951, h3144, h3227, hlam]
                    · linarith only [h0, h2940, h3225, h3226, hc24, hlam, hphi, ht45, u5elo2]
                  · linarith only [h0, h3142, h3225, hlam]
            · linarith only [h0, h2940, h2942, h3145, hc14, hlam, hphi, ht45, u5elo3]
          · linarith only [h0, h2940, h2942, h3144, hlam]
        · linarith only [h0, h2940, h3143, hc14, hlam, hphi, ht45, u5elo2]
      · linarith only [h0, h2940, h3142, hlam]
  · linarith only [h2940, h2941, hc14, hlam, hphi, ht45, u5elo1]

end R2N4
