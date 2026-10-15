import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5416000 in
set_option maxHeartbeats 5416000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s4_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3095 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3633 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h3634 | h3634
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3635 | h3635
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3636 | h3636
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3637 | h3637
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3638 | h3638
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3639 | h3639
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3640 | h3640
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3641 | h3641
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3642 | h3642
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3643 | h3643
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3644 | h3644
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3645 | h3645
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3646 | h3646
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3647 | h3647
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3648 | h3648
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3649 | h3649
                                · rcases h0bigk with h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [hlam, p3650_0]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h0, hlam, p3650_1]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h3095, hlam, p3650_0]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h3095, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p3650_1]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h3095, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p3650_1]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p3650_1]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [hlam, p3650_0]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h0, h3095, h3633, h3642, h3646, h3649, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3650_1]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h0, h3633, h3642, h3646, h3649, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3650_1]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    rcases p3650_3 (m.d 0 1) (by simp) with h3660 | h3660
                                    · linarith only [h0, h3660, hlam]
                                    · linarith only [h3634, h3660, hlam]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h3633, h3642, h3646, h3649, hc03, hc45, hlam, hphi, ht0b, ht5b, p3650_1]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h3635, hlam, p3650_1]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [hlam, p3650_0]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h3095, h3633, h3641, h3642, h3646, h3649, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3650_1]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    rcases p3650_3 (m.d 0 1) (by simp) with h3667 | h3667
                                    · linarith only [h3095, h3667, hlam]
                                    · linarith only [h3634, h3667, hlam]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h3633, hlam, p3650_0]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h3636, hlam, p3650_0]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h3638, hlam, p3650_0]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [hlam, p3650_0]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h0, h3633, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3650_1]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h3634, hlam, p3650_0]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h3637, hlam, p3650_1]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h3639, hlam, p3650_0]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [h3640, hlam, p3650_1]
                                  · have p3650_0 := h3650c.1
                                    have p3650_1 := h3650c.2.1
                                    have p3650_2 := h3650c.2.2.1
                                    have p3650_3 := h3650c.2.2.2
                                    linarith only [hlam, p3650_0]
                                · linarith only [h3095, h3633, h3641, h3645, h3649, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h3095, h3633, h3641, h3645, h3646, h3648, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h3639, h3646, h3647, hc34, hlam, hphi, ht45, u5elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3683 | h3683
                            · linarith only [h3095, h3633, h3641, h3644, h3646, h3683, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3685 | h3685
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3686 | h3686
                                · rcases h0bigk with h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [hlam, p3687_0]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h0, hlam, p3687_1]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h3095, hlam, p3687_0]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h3095, h3641, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3687_1]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h3095, h3641, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3687_1]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p3687_1]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [hlam, p3687_0]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h0, h3095, h3633, h3644, h3646, h3685, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3687_1]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h0, h3633, h3644, h3646, h3685, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3687_1]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h0, h3639, h3683, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3687_1]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h3633, h3644, h3646, h3685, hc03, hc45, hlam, hphi, ht0b, ht5b, p3687_1]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h3635, hlam, p3687_1]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [hlam, p3687_0]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h0, h3633, h3635, h3644, h3646, h3685, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3687_1]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h0, h3635, h3639, h3683, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3687_1]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h3633, hlam, p3687_0]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h3636, hlam, p3687_0]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h3638, hlam, p3687_0]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [hlam, p3687_0]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h3639, h3683, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3687_1]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h3634, hlam, p3687_0]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h3637, hlam, p3687_1]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h3639, hlam, p3687_0]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [h3640, hlam, p3687_1]
                                  · have p3687_0 := h3687c.1
                                    have p3687_1 := h3687c.2.1
                                    have p3687_2 := h3687c.2.2.1
                                    have p3687_3 := h3687c.2.2.2
                                    linarith only [hlam, p3687_0]
                                · linarith only [h3095, h3633, h3641, h3645, h3646, h3686, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h3095, h3633, h3641, h3645, h3646, h3685, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3715 | h3715
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3716 | h3716
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3717 | h3717
                              · linarith only [h3642, h3645, h3717, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3719 | h3719
                                · linarith only [h3642, h3645, h3715, h3719, hlam]
                                · rcases h0bigk with h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c | h3721c
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [hlam, p3721_0]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h0, hlam, p3721_1]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h3095, hlam, p3721_0]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h3095, h3641, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3721_1]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h3095, h3640, h3641, h3642, h3645, h3715, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3721_1]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p3721_1]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [hlam, p3721_0]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h0, h3095, hc01, hc12, hlam, hphi, p3721_1]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h0, h3640, h3642, h3645, h3715, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3721_1]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h0, h3640, h3642, h3645, h3715, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3721_1]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h3633, h3640, h3642, h3645, h3715, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3721_1]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h3635, hlam, p3721_1]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [hlam, p3721_0]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h3095, h3640, h3641, h3642, h3645, h3715, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3721_1]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h3095, h3640, h3641, h3642, h3645, h3715, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3721_1]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h3633, hlam, p3721_0]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h3636, hlam, p3721_0]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h3638, hlam, p3721_0]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [hlam, p3721_0]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h3633, h3640, h3642, h3645, h3715, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3721_1]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h3634, hlam, p3721_0]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h3637, hlam, p3721_1]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h3639, hlam, p3721_0]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [h3640, hlam, p3721_1]
                                  · have p3721_0 := h3721c.1
                                    have p3721_1 := h3721c.2.1
                                    have p3721_2 := h3721c.2.2.1
                                    have p3721_3 := h3721c.2.2.2
                                    linarith only [hlam, p3721_0]
                            · linarith only [h3639, h3715, h3716, hc34, hlam, hphi, ht45, u5elo0]
                          · linarith only [h3095, h3633, h3640, h3641, h3644, h3645, h3715, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h3095, h3638, h3644, hlam]
                    · linarith only [h3095, h3641, h3643, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h3636, h3642, hlam]
                · linarith only [h0, h3635, h3641, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3753 | h3753
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3754 | h3754
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3755 | h3755
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3756 | h3756
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3757 | h3757
                        · linarith only [h3095, h3633, h3640, h3753, h3757, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3759 | h3759
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3760 | h3760
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3761 | h3761
                              · linarith only [h3633, h3640, h3754, h3761, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3763 | h3763
                                · linarith only [h3633, h3640, h3754, h3759, h3763, hlam]
                                · rcases h0bigk with h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c | h3765c
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [hlam, p3765_0]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [h0, hlam, p3765_1]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [h3095, hlam, p3765_0]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [h3095, h3633, h3753, h3754, h3759, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3765_1]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [h3095, h3633, h3640, h3753, h3754, h3759, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3765_1]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p3765_1]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [hlam, p3765_0]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [h0, h3095, hc01, hc12, hlam, hphi, p3765_1]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    rcases p3765_3 (m.d 0 1) (by simp) with h3774 | h3774
                                    · linarith only [h0, h3774, hlam]
                                    · linarith only [h3633, h3774, hlam]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    rcases p3765_3 (m.d 0 1) (by simp) with h3777 | h3777
                                    · linarith only [h0, h3777, hlam]
                                    · linarith only [h3634, h3777, hlam]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [h3634, h3754, h3757, h3759, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3765_1]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [h3635, hlam, p3765_1]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [hlam, p3765_0]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    rcases p3765_3 (m.d 0 1) (by simp) with h3783 | h3783
                                    · linarith only [h3095, h3783, hlam]
                                    · linarith only [h3633, h3783, hlam]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    rcases p3765_3 (m.d 0 1) (by simp) with h3786 | h3786
                                    · linarith only [h3095, h3786, hlam]
                                    · linarith only [h3634, h3786, hlam]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [h3633, hlam, p3765_0]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [h3636, hlam, p3765_0]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [h3638, hlam, p3765_0]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [hlam, p3765_0]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [h3640, hlam, p3765_0]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [h3634, hlam, p3765_0]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [h3637, hlam, p3765_1]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [h3639, hlam, p3765_0]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [h3633, h3754, h3759, hc34, hlam, hphi, ht45, p3765_1, u5elo0]
                                  · have p3765_0 := h3765c.1
                                    have p3765_1 := h3765c.2.1
                                    have p3765_2 := h3765c.2.2.1
                                    have p3765_3 := h3765c.2.2.2
                                    linarith only [hlam, p3765_0]
                            · linarith only [h3639, h3640, h3759, h3760, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h3638, h3640, h3759, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h3095, h3638, h3640, h3756, hc03, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h3755, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h3095, h3634, h3636, h3753, h3754, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h3635, h3753, hlam]
            · linarith only [h3095, h3633, h3639, hc14, hlam, hphi, ht45, u5elo3]
          · linarith only [h3095, h3633, h3638, hlam]
        · linarith only [h0, h3633, h3637, hc14, hlam, hphi, ht45, u5elo2]
      · linarith only [h3095, h3633, h3635, h3636, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3809 | h3809
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3810 | h3810
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3811 | h3811
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3812 | h3812
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3813 | h3813
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3814 | h3814
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3815 | h3815
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3816 | h3816
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3817 | h3817
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3818 | h3818
                        · linarith only [h0, h3633, h3635, h3814, h3818, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h3633, h3635, h3813, h3814, h3818, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h3634, h3635, h3811, h3814, h3817, hc03, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h3633, h3635, h3814, h3815, h3816, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h3633, h3635, h3814, h3815, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3824 | h3824
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3825 | h3825
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3826 | h3826
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3827 | h3827
                        · linarith only [h0, h3633, h3814, h3827, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h3633, h3813, h3814, h3826, h3827, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h3095, h3811, h3826, hlam]
                    · linarith only [h0, h3825, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h3633, h3809, h3824, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3833 | h3833
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3834 | h3834
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3835 | h3835
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3836 | h3836
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3837 | h3837
                        · linarith only [h0, h3633, h3635, h3833, h3837, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3839 | h3839
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3840 | h3840
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3841 | h3841
                              · linarith only [h3813, h3834, h3837, h3841, hc04, hlam, hphi, ht45, u5elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3843 | h3843
                                · linarith only [h3635, h3811, h3813, h3833, h3843, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases h0bigk with h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [hlam, p3845_0]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h0, hlam, p3845_1]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h3095, hlam, p3845_0]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h0, h3633, h3635, h3833, h3834, h3839, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3845_1]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h0, h3635, h3833, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3845_1]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h3635, h3833, hc01, hc12, hlam, hphi, p3845_1]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [hlam, p3845_0]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h3635, hlam, p3845_0]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h3633, h3635, h3833, h3834, h3839, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3845_1]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h3634, h3635, h3833, h3835, h3840, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3845_1]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h3633, h3635, h3833, h3834, h3839, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3845_1]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h3635, h3833, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3845_1]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [hlam, p3845_0]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h3633, h3635, h3833, h3834, h3839, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3845_1]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h3634, h3635, h3833, h3835, h3840, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3845_1]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h3633, hlam, p3845_0]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h3809, hlam, p3845_0]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h3811, hlam, p3845_0]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [hlam, p3845_0]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h3813, hlam, p3845_0]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h3634, hlam, p3845_0]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h3810, hlam, p3845_1]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h3812, hlam, p3845_0]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [h3633, h3834, h3839, hc34, hlam, hphi, ht45, p3845_1, u5elo0]
                                  · have p3845_0 := h3845c.1
                                    have p3845_1 := h3845c.2.1
                                    have p3845_2 := h3845c.2.2.1
                                    have p3845_3 := h3845c.2.2.2
                                    linarith only [hlam, p3845_0]
                            · linarith only [h3095, h3634, h3635, h3834, h3837, h3839, h3840, hc34, hlam, hphi, ht45, u5elo3]
                          · linarith only [h0, h3634, h3635, h3811, h3837, h3839, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h3811, h3813, h3836, hc13, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h3635, h3833, h3835, hc03, hlam, hphi, ht34, ht45, u5elo2]
                  · linarith only [h0, h3635, h3833, h3834, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3876 | h3876
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3877 | h3877
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3878 | h3878
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3879 | h3879
                        · linarith only [h0, h3633, h3833, h3879, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3881 | h3881
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3882 | h3882
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3883 | h3883
                              · linarith only [h3633, h3813, h3876, h3883, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3885 | h3885
                                · linarith only [h3633, h3813, h3876, h3881, h3885, hlam]
                                · rcases h0bigk with h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c | h3887c
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h0, hlam, p3887_1]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3095, hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h0, h3833, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3887_1]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h0, h3633, h3813, h3833, h3876, h3881, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3887_1]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3634, h3635, hc03, hc15, hlam, hphi, ht0b, ht5b, p3887_1]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3635, hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h0, h3633, h3833, h3876, h3881, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3887_1]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h0, h3633, h3813, h3833, h3876, h3881, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3887_1]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3633, h3635, h3876, h3881, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3887_1]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3635, hc02, hc23, hlam, hphi, p3887_1]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    rcases p3887_3 (m.d 0 1) (by simp) with h3901 | h3901
                                    · linarith only [h3095, h3901, hlam]
                                    · linarith only [h3633, h3901, hlam]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    rcases p3887_3 (m.d 0 1) (by simp) with h3904 | h3904
                                    · linarith only [h3095, h3904, hlam]
                                    · linarith only [h3634, h3904, hlam]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3633, hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3809, hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3811, hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3813, hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3634, hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3810, hlam, p3887_1]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3812, hlam, p3887_0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [h3633, h3876, h3881, hc34, hlam, hphi, ht45, p3887_1, u5elo0]
                                  · have p3887_0 := h3887c.1
                                    have p3887_1 := h3887c.2.1
                                    have p3887_2 := h3887c.2.2.1
                                    have p3887_3 := h3887c.2.2.2
                                    linarith only [hlam, p3887_0]
                            · linarith only [h3833, h3882, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                          · linarith only [h0, h3634, h3833, h3876, h3879, h3881, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h3095, h3811, h3813, h3878, hc03, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h3877, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h3633, h3809, h3876, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h3095, h3633, h3812, hc14, hlam, hphi, ht45, u5elo3]
          · linarith only [h0, h3633, h3635, h3811, hlam]
        · linarith only [h0, h3633, h3810, hc14, hlam, hphi, ht45, u5elo2]
      · linarith only [h0, h3633, h3809, hlam]
  · linarith only [h3633, h3634, hc14, hlam, hphi, ht45, u5elo1]

end R2N4
