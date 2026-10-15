import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9252000 in
set_option maxHeartbeats 9252000 in
theorem r1l7_22_14_H_I_L_I_s2_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3667 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3668 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3669 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3670 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h3671 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h3672 | h3672
  · rcases m.htr 1 2 3 (by decide) (by decide) with h3673 | h3673
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3674 | h3674
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3675 | h3675
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3676 | h3676
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3677 | h3677
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3678 | h3678
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3679 | h3679
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3680 | h3680
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3681 | h3681
                    · rcases h2bigk with h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c | h3682c
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [hlam, p3682_0]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h0, hlam, p3682_1]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h3678, h3681, hc02, hc45, hlam, hphi, ht0b, ht5b, p3682_1]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h0, h3678, h3681, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3682_1]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        rcases p3682_3 (m.d 0 2) (by simp) with h3687 | h3687
                        · rcases p3682_3 (m.d 1 2) (by simp) with h3688 | h3688
                          · rcases p3682_3 (m.d 2 3) (by simp) with h3689 | h3689
                            · linarith only [h3668, h3689, hlam]
                            · linarith only [h3679, h3689, hlam]
                          · linarith only [h3675, h3688, hlam]
                        · linarith only [h3687, hlam, p3682_0]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h0, h3667, h3674, h3678, h3681, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3682_1]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [hlam, p3682_0]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h3678, h3681, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3682_1]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h3678, h3681, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3682_1]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        rcases p3682_3 (m.d 0 2) (by simp) with h3698 | h3698
                        · linarith only [h0, h3698, hlam]
                        · linarith only [h3670, h3698, hlam]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h3668, hlam, p3682_0]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h3673, hlam, p3682_0]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [hlam, p3682_0]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h3668, h3678, h3681, hc02, hc45, hlam, hphi, ht0b, ht5b, p3682_1]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h0, h3668, h3679, h3681, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3682_1]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h3669, hlam, p3682_0]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h3674, hlam, p3682_0]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h3678, hlam, p3682_1]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [hlam, p3682_0]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h3667, h3674, h3679, h3681, hc01, hc45, hlam, hphi, ht0b, ht5b, p3682_1]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h3670, hlam, p3682_0]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h3675, hlam, p3682_0]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h3679, hlam, p3682_1]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [h3680, hlam, p3682_0]
                      · have p3682_0 := h3682c.1
                        have p3682_1 := h3682c.2.1
                        have p3682_2 := h3682c.2.2.1
                        have p3682_3 := h3682c.2.2.2
                        linarith only [hlam, p3682_0]
                    · linarith only [h0, h3667, h3677, h3681, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h3667, h3677, h3680, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3718 | h3718
                  · linarith only [h3678, h3679, h3718, hlam]
                  · linarith only [h0, h3667, h3677, h3718, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3721 | h3721
                · linarith only [h0, h3667, h3676, h3678, h3721, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3723 | h3723
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3724 | h3724
                    · rcases h2bigk with h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c | h3725c
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [hlam, p3725_0]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [h0, hlam, p3725_1]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        rcases p3725_3 (m.d 0 2) (by simp) with h3728 | h3728
                        · rcases p3725_3 (m.d 1 2) (by simp) with h3729 | h3729
                          · rcases p3725_3 (m.d 2 3) (by simp) with h3730 | h3730
                            · linarith only [h3730, hlam, p3725_0]
                            · rcases p3725_3 (m.d 2 4) (by simp) with h3732 | h3732
                              · linarith only [h3669, h3732, hlam]
                              · linarith only [h3678, h3732, hlam]
                          · linarith only [h3673, h3729, hlam]
                        · linarith only [h3728, hlam, p3725_0]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [h0, h3723, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3725_1]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        rcases p3725_3 (m.d 0 2) (by simp) with h3738 | h3738
                        · rcases p3725_3 (m.d 1 2) (by simp) with h3739 | h3739
                          · rcases p3725_3 (m.d 2 3) (by simp) with h3740 | h3740
                            · linarith only [h3668, h3740, hlam]
                            · rcases p3725_3 (m.d 2 4) (by simp) with h3742 | h3742
                              · linarith only [h3669, h3742, hlam]
                              · linarith only [h3723, h3742, hlam]
                          · linarith only [h3675, h3739, hlam]
                        · linarith only [h3738, hlam, p3725_0]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [h0, h3667, h3676, h3721, h3724, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3725_1]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [hlam, p3725_0]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        rcases p3725_3 (m.d 0 2) (by simp) with h3749 | h3749
                        · linarith only [h0, h3749, hlam]
                        · linarith only [h3668, h3749, hlam]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [h3723, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3725_1]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        rcases p3725_3 (m.d 0 2) (by simp) with h3753 | h3753
                        · linarith only [h0, h3753, hlam]
                        · linarith only [h3670, h3753, hlam]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [h3668, hlam, p3725_0]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [h3673, hlam, p3725_0]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [hlam, p3725_0]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [h3678, hlam, p3725_0]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [h3721, hlam, p3725_0]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [h3669, hlam, p3725_0]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [h3674, hlam, p3725_0]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [h3669, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3725_1]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [hlam, p3725_0]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [h3667, h3676, h3678, h3721, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3725_1]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [h3670, hlam, p3725_0]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [h3675, hlam, p3725_0]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [h0, h3670, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3725_1]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [h3723, hlam, p3725_0]
                      · have p3725_0 := h3725c.1
                        have p3725_1 := h3725c.2.1
                        have p3725_2 := h3725c.2.2.1
                        have p3725_3 := h3725c.2.2.2
                        linarith only [hlam, p3725_0]
                    · linarith only [h0, h3667, h3677, h3678, h3724, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h3667, h3677, h3678, h3723, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3773 | h3773
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3774 | h3774
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3775 | h3775
                  · linarith only [h3674, h3677, h3775, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3777 | h3777
                    · linarith only [h0, h3668, h3677, h3773, h3777, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases h2bigk with h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [hlam, p3779_0]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [h0, hlam, p3779_1]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [h0, h3773, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3779_1]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        rcases p3779_3 (m.d 0 2) (by simp) with h3783 | h3783
                        · rcases p3779_3 (m.d 1 2) (by simp) with h3784 | h3784
                          · rcases p3779_3 (m.d 2 3) (by simp) with h3785 | h3785
                            · linarith only [h3668, h3785, hlam]
                            · linarith only [h3773, h3785, hlam]
                          · linarith only [h3674, h3784, hlam]
                        · linarith only [h3783, hlam, p3779_0]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        rcases p3779_3 (m.d 0 2) (by simp) with h3790 | h3790
                        · rcases p3779_3 (m.d 1 2) (by simp) with h3791 | h3791
                          · rcases p3779_3 (m.d 2 3) (by simp) with h3792 | h3792
                            · linarith only [h3668, h3792, hlam]
                            · linarith only [h3774, h3792, hlam]
                          · linarith only [h3675, h3791, hlam]
                        · linarith only [h3790, hlam, p3779_0]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p3779_1]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [hlam, p3779_0]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [h3774, h3777, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3779_1]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        rcases p3779_3 (m.d 0 2) (by simp) with h3800 | h3800
                        · linarith only [h0, h3800, hlam]
                        · linarith only [h3669, h3800, hlam]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        rcases p3779_3 (m.d 0 2) (by simp) with h3803 | h3803
                        · linarith only [h0, h3803, hlam]
                        · linarith only [h3670, h3803, hlam]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [h3668, hlam, p3779_0]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [h3673, hlam, p3779_0]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [hlam, p3779_0]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [h3668, h3773, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3779_1]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [h0, h3668, h3773, h3775, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3779_1]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [h3669, hlam, p3779_0]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [h3674, hlam, p3779_0]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [h3773, hlam, p3779_1]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [hlam, p3779_0]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [h3775, hlam, p3779_1]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [h3670, hlam, p3779_0]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [h3675, hlam, p3779_0]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [h3774, hlam, p3779_1]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [h0, h3670, h3773, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3779_1]
                      · have p3779_0 := h3779c.1
                        have p3779_1 := h3779c.2.1
                        have p3779_2 := h3779c.2.2.1
                        have p3779_3 := h3779c.2.2.2
                        linarith only [hlam, p3779_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3821 | h3821
                  · linarith only [h0, h3667, h3674, h3675, h3677, h3773, h3774, h3821, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3823 | h3823
                    · linarith only [h3675, h3677, h3773, h3774, h3823, hlam]
                    · linarith only [h0, h3667, h3672, h3773, h3774, h3823, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h0, h3667, h3672, h3676, h3677, h3773, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3827 | h3827
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3828 | h3828
              · linarith only [h3673, h3676, h3828, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3830 | h3830
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3831 | h3831
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3832 | h3832
                    · rcases h2bigk with h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [hlam, p3833_0]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h0, hlam, p3833_1]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h0, h3830, h3832, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3833_1]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h0, h3828, h3830, h3832, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3833_1]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        rcases p3833_3 (m.d 0 2) (by simp) with h3838 | h3838
                        · rcases p3833_3 (m.d 1 2) (by simp) with h3839 | h3839
                          · rcases p3833_3 (m.d 2 3) (by simp) with h3840 | h3840
                            · linarith only [h3668, h3840, hlam]
                            · linarith only [h3830, h3840, hlam]
                          · linarith only [h3675, h3839, hlam]
                        · linarith only [h3838, hlam, p3833_0]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p3833_1]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [hlam, p3833_0]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h3830, h3832, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3833_1]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h3828, h3830, h3832, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3833_1]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        rcases p3833_3 (m.d 0 2) (by simp) with h3849 | h3849
                        · linarith only [h0, h3849, hlam]
                        · linarith only [h3670, h3849, hlam]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h3668, hlam, p3833_0]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h3673, hlam, p3833_0]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [hlam, p3833_0]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h3828, hlam, p3833_0]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h3667, h3671, h3673, h3676, hc01, hc25, hlam, hphi, ht0b, ht5b, p3833_1]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h3669, hlam, p3833_0]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h3674, hlam, p3833_0]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h3830, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p3833_1]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [hlam, p3833_0]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h0, h3667, h3674, h3830, h3832, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3833_1]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h3670, hlam, p3833_0]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h3675, hlam, p3833_0]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h3830, hlam, p3833_1]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [h3831, hlam, p3833_0]
                      · have p3833_0 := h3833c.1
                        have p3833_1 := h3833c.2.1
                        have p3833_2 := h3833c.2.2.1
                        have p3833_3 := h3833c.2.2.2
                        linarith only [hlam, p3833_0]
                    · linarith only [h0, h3667, h3672, h3676, h3832, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h3667, h3827, h3831, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3869 | h3869
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3870 | h3870
                    · rcases h2bigk with h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [hlam, p3871_0]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [h0, hlam, p3871_1]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        rcases p3871_3 (m.d 0 2) (by simp) with h3874 | h3874
                        · rcases p3871_3 (m.d 1 2) (by simp) with h3875 | h3875
                          · rcases p3871_3 (m.d 2 3) (by simp) with h3876 | h3876
                            · linarith only [h3876, hlam, p3871_0]
                            · rcases p3871_3 (m.d 2 4) (by simp) with h3878 | h3878
                              · linarith only [h3669, h3878, hlam]
                              · linarith only [h3828, h3878, hlam]
                          · linarith only [h3673, h3875, hlam]
                        · linarith only [h3874, hlam, p3871_0]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [h0, h3869, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3871_1]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        rcases p3871_3 (m.d 0 2) (by simp) with h3884 | h3884
                        · rcases p3871_3 (m.d 1 2) (by simp) with h3885 | h3885
                          · rcases p3871_3 (m.d 2 3) (by simp) with h3886 | h3886
                            · linarith only [h3668, h3886, hlam]
                            · rcases p3871_3 (m.d 2 4) (by simp) with h3888 | h3888
                              · linarith only [h3669, h3888, hlam]
                              · linarith only [h3869, h3888, hlam]
                          · linarith only [h3675, h3885, hlam]
                        · linarith only [h3884, hlam, p3871_0]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p3871_1]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [hlam, p3871_0]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        rcases p3871_3 (m.d 0 2) (by simp) with h3895 | h3895
                        · linarith only [h0, h3895, hlam]
                        · linarith only [h3668, h3895, hlam]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [h3869, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3871_1]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        rcases p3871_3 (m.d 0 2) (by simp) with h3899 | h3899
                        · linarith only [h0, h3899, hlam]
                        · linarith only [h3670, h3899, hlam]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [h3668, hlam, p3871_0]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [h3673, hlam, p3871_0]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [hlam, p3871_0]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [h3828, hlam, p3871_0]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [h3830, hlam, p3871_0]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [h3669, hlam, p3871_0]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [h3674, hlam, p3871_0]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [h3667, h3674, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3871_1]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [hlam, p3871_0]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [h0, h3667, h3674, h3830, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3871_1]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [h3670, hlam, p3871_0]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [h3675, hlam, p3871_0]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [h3670, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3871_1]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [h3869, hlam, p3871_0]
                      · have p3871_0 := h3871c.1
                        have p3871_1 := h3871c.2.1
                        have p3871_2 := h3871c.2.2.1
                        have p3871_3 := h3871c.2.2.2
                        linarith only [hlam, p3871_0]
                    · linarith only [h0, h3667, h3672, h3673, h3676, h3870, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h3667, h3827, h3869, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3919 | h3919
              · linarith only [h3673, h3676, h3919, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3921 | h3921
                · linarith only [h0, h3667, h3672, h3674, h3827, h3919, h3921, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3923 | h3923
                  · linarith only [h3674, h3827, h3923, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3925 | h3925
                    · rcases h2bigk with h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c | h3926c
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [hlam, p3926_0]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [h0, hlam, p3926_1]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        rcases p3926_3 (m.d 0 2) (by simp) with h3929 | h3929
                        · rcases p3926_3 (m.d 1 2) (by simp) with h3930 | h3930
                          · rcases p3926_3 (m.d 2 3) (by simp) with h3931 | h3931
                            · linarith only [h3931, hlam, p3926_0]
                            · rcases p3926_3 (m.d 2 4) (by simp) with h3933 | h3933
                              · linarith only [h3669, h3933, hlam]
                              · linarith only [h3919, h3933, hlam]
                          · linarith only [h3673, h3930, hlam]
                        · linarith only [h3929, hlam, p3926_0]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        rcases p3926_3 (m.d 0 2) (by simp) with h3938 | h3938
                        · rcases p3926_3 (m.d 1 2) (by simp) with h3939 | h3939
                          · rcases p3926_3 (m.d 2 3) (by simp) with h3940 | h3940
                            · linarith only [h3668, h3940, hlam]
                            · rcases p3926_3 (m.d 2 4) (by simp) with h3942 | h3942
                              · linarith only [h3942, hlam, p3926_0]
                              · rcases p3926_3 (m.d 2 5) (by simp) with h3944 | h3944
                                · linarith only [h3670, h3944, hlam]
                                · linarith only [h3923, h3944, hlam]
                          · linarith only [h3674, h3939, hlam]
                        · linarith only [h3938, hlam, p3926_0]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        rcases p3926_3 (m.d 0 2) (by simp) with h3949 | h3949
                        · rcases p3926_3 (m.d 1 2) (by simp) with h3950 | h3950
                          · rcases p3926_3 (m.d 2 3) (by simp) with h3951 | h3951
                            · linarith only [h3668, h3951, hlam]
                            · rcases p3926_3 (m.d 2 4) (by simp) with h3953 | h3953
                              · linarith only [h3669, h3953, hlam]
                              · rcases p3926_3 (m.d 2 5) (by simp) with h3955 | h3955
                                · linarith only [h3955, hlam, p3926_0]
                                · rcases h4bigk with h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [hlam, p3957_0]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    rcases p3957_3 (m.d 0 4) (by simp) with h3959 | h3959
                                    · rcases p3957_3 (m.d 1 4) (by simp) with h3960 | h3960
                                      · linarith only [h3667, h3960, hlam]
                                      · rcases p3957_3 (m.d 2 4) (by simp) with h3962 | h3962
                                        · linarith only [h3669, h3962, hlam]
                                        · rcases p3957_3 (m.d 3 4) (by simp) with h3964 | h3964
                                          · linarith only [h3671, h3964, hlam]
                                          · linarith only [h3676, h3964, hlam]
                                    · linarith only [h3667, h3959, hlam]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    rcases p3957_3 (m.d 0 4) (by simp) with h3968 | h3968
                                    · rcases p3957_3 (m.d 1 4) (by simp) with h3969 | h3969
                                      · linarith only [h3667, h3969, hlam]
                                      · linarith only [h3674, h3969, hlam]
                                    · linarith only [h3669, h3968, hlam]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [h0, h3667, h3827, h3925, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3957_1]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [h0, h3667, h3674, h3827, h3919, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3957_1]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [h3667, hlam, p3957_1]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [hlam, p3957_0]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [h3827, h3919, h3925, hc23, hc34, hlam, hphi, p3957_1]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [h3676, hlam, p3957_1]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [h3827, hlam, p3957_0]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [h3669, hlam, p3957_1]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [h3674, hlam, p3957_1]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [hlam, p3957_0]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [h3919, hlam, p3957_1]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [h3923, hlam, p3957_0]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [h3671, hlam, p3957_1]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    rcases p3957_3 (m.d 0 4) (by simp) with h3986 | h3986
                                    · rcases p3957_3 (m.d 1 4) (by simp) with h3987 | h3987
                                      · linarith only [h3676, h3987, hlam]
                                      · rcases p3957_3 (m.d 2 4) (by simp) with h3989 | h3989
                                        · linarith only [h3919, h3989, hlam]
                                        · rcases p3957_3 (m.d 3 4) (by simp) with h3991 | h3991
                                          · rcases p3957_3 (m.d 4 5) (by simp) with h3992 | h3992
                                            · linarith only [h3925, h3992, hlam]
                                            · linarith only [h3827, h3992, hlam]
                                          · linarith only [h3676, h3991, hlam]
                                    · linarith only [h3667, h3986, hlam]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    rcases p3957_3 (m.d 0 4) (by simp) with h3997 | h3997
                                    · rcases p3957_3 (m.d 1 4) (by simp) with h3998 | h3998
                                      · linarith only [h3676, h3998, hlam]
                                      · linarith only [h3674, h3998, hlam]
                                    · linarith only [h3669, h3997, hlam]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [hlam, p3957_0]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [h0, h3668, h3671, h3827, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3957_1]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [h3672, hlam, p3957_0]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [h0, h3667, h3672, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3957_1]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [h0, h3667, h3672, h3919, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3957_1]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [h3925, hlam, p3957_0]
                                  · have p3957_0 := h3957c.1
                                    have p3957_1 := h3957c.2.1
                                    have p3957_2 := h3957c.2.2.1
                                    have p3957_3 := h3957c.2.2.2
                                    linarith only [hlam, p3957_0]
                          · linarith only [h3675, h3950, hlam]
                        · linarith only [h3949, hlam, p3926_0]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [h3668, h3671, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3926_1]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [hlam, p3926_0]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        rcases p3926_3 (m.d 0 2) (by simp) with h4013 | h4013
                        · linarith only [h0, h4013, hlam]
                        · linarith only [h3668, h4013, hlam]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        rcases p3926_3 (m.d 0 2) (by simp) with h4016 | h4016
                        · linarith only [h0, h4016, hlam]
                        · linarith only [h3669, h4016, hlam]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        rcases p3926_3 (m.d 0 2) (by simp) with h4019 | h4019
                        · linarith only [h0, h4019, hlam]
                        · linarith only [h3670, h4019, hlam]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [h3668, hlam, p3926_0]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [h3673, hlam, p3926_0]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [hlam, p3926_0]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [h3919, hlam, p3926_0]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [h3921, hlam, p3926_0]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [h3669, hlam, p3926_0]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [h3674, hlam, p3926_0]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [h0, h3667, h3674, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3926_1]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [hlam, p3926_0]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [h3923, hlam, p3926_1]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [h3670, hlam, p3926_0]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [h3675, hlam, p3926_0]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [h0, h3668, h3671, h3675, h3827, h3925, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3926_1]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [h0, h3668, h3671, h3675, h3827, h3925, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3926_1]
                      · have p3926_0 := h3926c.1
                        have p3926_1 := h3926c.2.1
                        have p3926_2 := h3926c.2.2.1
                        have p3926_3 := h3926c.2.2.2
                        linarith only [hlam, p3926_0]
                    · linarith only [h0, h3667, h3672, h3673, h3676, h3925, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
        · linarith only [h0, h3670, h3675, hlam]
      · linarith only [h0, h3669, h3674, hlam]
    · linarith only [h0, h3668, h3673, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4041 | h4041
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4042 | h4042
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4043 | h4043
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4044 | h4044
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4045 | h4045
            · linarith only [h0, h3667, h3672, h4045, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4047 | h4047
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4048 | h4048
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4049 | h4049
                  · linarith only [h3667, h3672, h4042, h4049, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4051 | h4051
                    · linarith only [h3671, h3672, h4051, hlam]
                    · rcases h2bigk with h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c | h4053c
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [hlam, p4053_0]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [h0, hlam, p4053_1]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [h0, h4047, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4053_1]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        rcases p4053_3 (m.d 0 2) (by simp) with h4057 | h4057
                        · rcases p4053_3 (m.d 1 2) (by simp) with h4058 | h4058
                          · rcases p4053_3 (m.d 2 3) (by simp) with h4059 | h4059
                            · linarith only [h3668, h4059, hlam]
                            · linarith only [h4047, h4059, hlam]
                          · linarith only [h4042, h4058, hlam]
                        · linarith only [h4057, hlam, p4053_0]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        rcases p4053_3 (m.d 0 2) (by simp) with h4064 | h4064
                        · rcases p4053_3 (m.d 1 2) (by simp) with h4065 | h4065
                          · rcases p4053_3 (m.d 2 3) (by simp) with h4066 | h4066
                            · linarith only [h3668, h4066, hlam]
                            · linarith only [h4048, h4066, hlam]
                          · linarith only [h4043, h4065, hlam]
                        · linarith only [h4064, hlam, p4053_0]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p4053_1]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [hlam, p4053_0]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [h4048, h4051, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4053_1]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        rcases p4053_3 (m.d 0 2) (by simp) with h4074 | h4074
                        · linarith only [h0, h4074, hlam]
                        · linarith only [h3669, h4074, hlam]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        rcases p4053_3 (m.d 0 2) (by simp) with h4077 | h4077
                        · linarith only [h0, h4077, hlam]
                        · linarith only [h3670, h4077, hlam]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [h3668, hlam, p4053_0]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [h4041, hlam, p4053_0]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [hlam, p4053_0]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [h3668, h4047, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4053_1]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [h0, h3668, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p4053_1]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [h3669, hlam, p4053_0]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [h4042, hlam, p4053_0]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [h4047, hlam, p4053_1]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [hlam, p4053_0]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [h4049, hlam, p4053_1]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [h3670, hlam, p4053_0]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [h4043, hlam, p4053_0]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [h4048, hlam, p4053_1]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [h0, h3670, h4047, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4053_1]
                      · have p4053_0 := h4053c.1
                        have p4053_1 := h4053c.2.1
                        have p4053_2 := h4053c.2.2.1
                        have p4053_3 := h4053c.2.2.2
                        linarith only [hlam, p4053_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4095 | h4095
                  · linarith only [h3667, h3672, h4042, h4095, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4097 | h4097
                    · linarith only [h3667, h3672, h4042, h4047, h4097, hlam]
                    · rcases h2bigk with h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c | h4099c
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [hlam, p4099_0]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h0, hlam, p4099_1]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h0, h4047, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4099_1]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        rcases p4099_3 (m.d 0 2) (by simp) with h4103 | h4103
                        · rcases p4099_3 (m.d 1 2) (by simp) with h4104 | h4104
                          · rcases p4099_3 (m.d 2 3) (by simp) with h4105 | h4105
                            · linarith only [h3668, h4105, hlam]
                            · linarith only [h4047, h4105, hlam]
                          · linarith only [h4042, h4104, hlam]
                        · linarith only [h4103, hlam, p4099_0]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h0, h4047, h4048, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4099_1]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p4099_1]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [hlam, p4099_0]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h4047, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4099_1]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        rcases p4099_3 (m.d 0 2) (by simp) with h4114 | h4114
                        · linarith only [h0, h4114, hlam]
                        · linarith only [h3669, h4114, hlam]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h4047, h4048, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4099_1]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h3668, hlam, p4099_0]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h4041, hlam, p4099_0]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [hlam, p4099_0]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h3670, h4047, h4048, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4099_1]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h4048, hlam, p4099_0]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h3669, hlam, p4099_0]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h4042, hlam, p4099_0]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h4047, hlam, p4099_1]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [hlam, p4099_0]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h4095, hlam, p4099_1]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h3670, hlam, p4099_0]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h4043, hlam, p4099_0]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h3670, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4099_1]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [h0, h3670, h4047, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4099_1]
                      · have p4099_0 := h4099c.1
                        have p4099_1 := h4099c.2.1
                        have p4099_2 := h4099c.2.2.1
                        have p4099_3 := h4099c.2.2.2
                        linarith only [hlam, p4099_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4133 | h4133
                · linarith only [h0, h3667, h4044, h4047, h4133, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4135 | h4135
                  · linarith only [h0, h3667, h3672, h4044, h4047, h4135, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4137 | h4137
                    · linarith only [h3667, h3672, h4044, h4137, hlam]
                    · rcases h2bigk with h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c | h4139c
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [hlam, p4139_0]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [h0, hlam, p4139_1]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        rcases p4139_3 (m.d 0 2) (by simp) with h4142 | h4142
                        · rcases p4139_3 (m.d 1 2) (by simp) with h4143 | h4143
                          · rcases p4139_3 (m.d 2 3) (by simp) with h4144 | h4144
                            · linarith only [h4144, hlam, p4139_0]
                            · rcases p4139_3 (m.d 2 4) (by simp) with h4146 | h4146
                              · linarith only [h3669, h4146, hlam]
                              · linarith only [h4047, h4146, hlam]
                          · linarith only [h4041, h4143, hlam]
                        · linarith only [h4142, hlam, p4139_0]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        rcases p4139_3 (m.d 0 2) (by simp) with h4151 | h4151
                        · rcases p4139_3 (m.d 1 2) (by simp) with h4152 | h4152
                          · rcases p4139_3 (m.d 2 3) (by simp) with h4153 | h4153
                            · linarith only [h3668, h4153, hlam]
                            · rcases p4139_3 (m.d 2 4) (by simp) with h4155 | h4155
                              · linarith only [h4155, hlam, p4139_0]
                              · rcases p4139_3 (m.d 2 5) (by simp) with h4157 | h4157
                                · linarith only [h3670, h4157, hlam]
                                · linarith only [h4135, h4157, hlam]
                          · linarith only [h4042, h4152, hlam]
                        · linarith only [h4151, hlam, p4139_0]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        rcases p4139_3 (m.d 0 2) (by simp) with h4162 | h4162
                        · rcases p4139_3 (m.d 1 2) (by simp) with h4163 | h4163
                          · rcases p4139_3 (m.d 2 3) (by simp) with h4164 | h4164
                            · linarith only [h3668, h4164, hlam]
                            · rcases p4139_3 (m.d 2 4) (by simp) with h4166 | h4166
                              · linarith only [h3669, h4166, hlam]
                              · rcases p4139_3 (m.d 2 5) (by simp) with h4168 | h4168
                                · linarith only [h4168, hlam, p4139_0]
                                · rcases h4bigk with h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c | h4170c
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [hlam, p4170_0]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h3672, hc14, hc45, hlam, hphi, p4170_1]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h3672, h4047, hc23, hc45, hlam, hphi, ht34, p4170_1]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h3672, hc34, hc45, hlam, hphi, p4170_1]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h3672, hlam, p4170_0]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h3667, hlam, p4170_1]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [hlam, p4170_0]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h0, h3667, h4047, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4170_1]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h0, h3667, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4170_1]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h4045, hlam, p4170_0]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h3669, hlam, p4170_1]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h4042, hlam, p4170_1]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [hlam, p4170_0]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h4047, hlam, p4170_1]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h4135, hlam, p4170_0]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h3671, hlam, p4170_1]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h4044, hlam, p4170_0]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h3671, h3672, h4047, hc23, hc45, hlam, hphi, ht34, p4170_1]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [hlam, p4170_0]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h4137, hlam, p4170_0]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h3667, h4044, h4047, hc23, hc45, hlam, hphi, ht34, p4170_1]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h4044, h4047, hc23, hc45, hlam, hphi, ht34, p4170_1]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    rcases p4170_3 (m.d 0 4) (by simp) with h4193 | h4193
                                    · linarith only [h3672, h4193, hlam]
                                    · linarith only [h3669, h4193, hlam]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [h4047, hc23, hc45, hlam, hphi, ht34, p4170_1]
                                  · have p4170_0 := h4170c.1
                                    have p4170_1 := h4170c.2.1
                                    have p4170_2 := h4170c.2.2.1
                                    have p4170_3 := h4170c.2.2.2
                                    linarith only [hlam, p4170_0]
                          · linarith only [h4043, h4163, hlam]
                        · linarith only [h4162, hlam, p4139_0]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p4139_1]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [hlam, p4139_0]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        rcases p4139_3 (m.d 0 2) (by simp) with h4202 | h4202
                        · linarith only [h0, h4202, hlam]
                        · linarith only [h3668, h4202, hlam]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        rcases p4139_3 (m.d 0 2) (by simp) with h4205 | h4205
                        · linarith only [h0, h4205, hlam]
                        · linarith only [h3669, h4205, hlam]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        rcases p4139_3 (m.d 0 2) (by simp) with h4208 | h4208
                        · linarith only [h0, h4208, hlam]
                        · linarith only [h3670, h4208, hlam]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [h3668, hlam, p4139_0]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [h4041, hlam, p4139_0]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [hlam, p4139_0]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [h4047, hlam, p4139_0]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [h4133, hlam, p4139_0]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [h3669, hlam, p4139_0]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [h4042, hlam, p4139_0]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [h3669, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4139_1]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [hlam, p4139_0]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [h4135, hlam, p4139_1]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [h3670, hlam, p4139_0]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [h4043, hlam, p4139_0]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [h0, h3670, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4139_1]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [h0, h3670, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4139_1]
                      · have p4139_0 := h4139c.1
                        have p4139_1 := h4139c.2.1
                        have p4139_2 := h4139c.2.2.1
                        have p4139_3 := h4139c.2.2.2
                        linarith only [hlam, p4139_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4226 | h4226
            · linarith only [h0, h3667, h3672, h4226, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4228 | h4228
              · linarith only [h4041, h4044, h4228, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4230 | h4230
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4231 | h4231
                  · linarith only [h3671, h3672, h4041, h4044, h4230, h4231, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h4228, h4230, h4231, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4234 | h4234
                  · linarith only [h0, h3669, h3671, h3672, h4044, h4234, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4236 | h4236
                    · linarith only [h3671, h3672, h4236, hlam]
                    · rcases h2bigk with h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [hlam, p4238_0]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [h0, hlam, p4238_1]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        rcases p4238_3 (m.d 0 2) (by simp) with h4241 | h4241
                        · rcases p4238_3 (m.d 1 2) (by simp) with h4242 | h4242
                          · rcases p4238_3 (m.d 2 3) (by simp) with h4243 | h4243
                            · linarith only [h4243, hlam, p4238_0]
                            · rcases p4238_3 (m.d 2 4) (by simp) with h4245 | h4245
                              · linarith only [h3669, h4245, hlam]
                              · linarith only [h4228, h4245, hlam]
                          · linarith only [h4041, h4242, hlam]
                        · linarith only [h4241, hlam, p4238_0]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        rcases p4238_3 (m.d 0 2) (by simp) with h4250 | h4250
                        · rcases p4238_3 (m.d 1 2) (by simp) with h4251 | h4251
                          · rcases p4238_3 (m.d 2 3) (by simp) with h4252 | h4252
                            · linarith only [h3668, h4252, hlam]
                            · rcases p4238_3 (m.d 2 4) (by simp) with h4254 | h4254
                              · linarith only [h4254, hlam, p4238_0]
                              · rcases p4238_3 (m.d 2 5) (by simp) with h4256 | h4256
                                · linarith only [h3670, h4256, hlam]
                                · linarith only [h4234, h4256, hlam]
                          · linarith only [h4042, h4251, hlam]
                        · linarith only [h4250, hlam, p4238_0]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        rcases p4238_3 (m.d 0 2) (by simp) with h4261 | h4261
                        · rcases p4238_3 (m.d 1 2) (by simp) with h4262 | h4262
                          · rcases p4238_3 (m.d 2 3) (by simp) with h4263 | h4263
                            · linarith only [h3668, h4263, hlam]
                            · rcases p4238_3 (m.d 2 4) (by simp) with h4265 | h4265
                              · linarith only [h3669, h4265, hlam]
                              · rcases p4238_3 (m.d 2 5) (by simp) with h4267 | h4267
                                · linarith only [h4267, hlam, p4238_0]
                                · rcases h4bigk with h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c | h4269c
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [hlam, p4269_0]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h3672, h4041, h4044, hc23, hc45, hlam, hphi, ht34, p4269_1]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h3672, h4228, hc23, hc45, hlam, hphi, ht34, p4269_1]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h3672, h4041, h4044, hc23, hc45, hlam, hphi, ht34, p4269_1]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h3672, hlam, p4269_0]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h3667, hlam, p4269_1]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [hlam, p4269_0]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h0, h3667, h4228, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4269_1]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h4044, hlam, p4269_1]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h4226, hlam, p4269_0]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h3669, hlam, p4269_1]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h4042, hlam, p4269_1]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [hlam, p4269_0]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h4228, hlam, p4269_1]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h4234, hlam, p4269_0]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h3671, hlam, p4269_1]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h3671, h3672, hc14, hc45, hlam, hphi, p4269_1]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h3671, h3672, h4228, hc23, hc45, hlam, hphi, ht34, p4269_1]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [hlam, p4269_0]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h4236, hlam, p4269_0]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h3671, h4041, h4044, hc23, hc45, hlam, hphi, ht34, p4269_1]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    rcases p4269_3 (m.d 0 4) (by simp) with h4291 | h4291
                                    · linarith only [h3672, h4291, hlam]
                                    · linarith only [h3667, h4291, hlam]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    rcases p4269_3 (m.d 0 4) (by simp) with h4294 | h4294
                                    · linarith only [h3672, h4294, hlam]
                                    · linarith only [h3669, h4294, hlam]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [h4041, h4044, hc23, hc45, hlam, hphi, ht34, p4269_1]
                                  · have p4269_0 := h4269c.1
                                    have p4269_1 := h4269c.2.1
                                    have p4269_2 := h4269c.2.2.1
                                    have p4269_3 := h4269c.2.2.2
                                    linarith only [hlam, p4269_0]
                          · linarith only [h4043, h4262, hlam]
                        · linarith only [h4261, hlam, p4238_0]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p4238_1]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [hlam, p4238_0]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        rcases p4238_3 (m.d 0 2) (by simp) with h4303 | h4303
                        · linarith only [h0, h4303, hlam]
                        · linarith only [h3668, h4303, hlam]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        rcases p4238_3 (m.d 0 2) (by simp) with h4306 | h4306
                        · linarith only [h0, h4306, hlam]
                        · linarith only [h3669, h4306, hlam]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        rcases p4238_3 (m.d 0 2) (by simp) with h4309 | h4309
                        · linarith only [h0, h4309, hlam]
                        · linarith only [h3670, h4309, hlam]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [h3668, hlam, p4238_0]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [h4041, hlam, p4238_0]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [hlam, p4238_0]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [h4228, hlam, p4238_0]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [h4230, hlam, p4238_0]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [h3669, hlam, p4238_0]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [h4042, hlam, p4238_0]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [h3667, h4042, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4238_1]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [hlam, p4238_0]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [h4234, hlam, p4238_1]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [h3670, hlam, p4238_0]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [h4043, hlam, p4238_0]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [h3670, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4238_1]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [h0, h3670, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4238_1]
                      · have p4238_0 := h4238c.1
                        have p4238_1 := h4238c.2.1
                        have p4238_2 := h4238c.2.2.1
                        have p4238_3 := h4238c.2.2.2
                        linarith only [hlam, p4238_0]
        · linarith only [h0, h3670, h4043, hlam]
      · linarith only [h0, h3669, h4042, hlam]
    · linarith only [h0, h3668, h4041, hlam]

end R2N4
