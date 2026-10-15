import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9934000 in
set_option maxHeartbeats 9934000 in
theorem r1l7_21_15_H_I_L_I_s3_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3093 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h3422 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h3633 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h3634 | h3634
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3635 | h3635
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3636 | h3636
      · linarith only [h0, h3636, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3638 | h3638
        · linarith only [h0, h3093, h3638, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3640 | h3640
          · linarith only [h0, h3422, h3640, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3642 | h3642
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3643 | h3643
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3644 | h3644
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3645 | h3645
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3646 | h3646
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3647 | h3647
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3648 | h3648
                        · rcases h1bigk with h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [hlam, p3649_0]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            rcases p3649_3 (m.d 0 1) (by simp) with h3651 | h3651
                            · rcases p3649_3 (m.d 1 2) (by simp) with h3652 | h3652
                              · linarith only [h3652, hlam, p3649_0]
                              · rcases p3649_3 (m.d 1 3) (by simp) with h3654 | h3654
                                · linarith only [h1, h3654, hlam]
                                · linarith only [h3636, h3654, hlam]
                            · linarith only [h3651, hlam, p3649_0]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h3642, h3648, hc01, hc45, hlam, hphi, ht0b, ht5b, p3649_1]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h3642, h3648, hc01, hc45, hlam, hphi, ht0b, ht5b, p3649_1]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            rcases p3649_3 (m.d 0 1) (by simp) with h3660 | h3660
                            · rcases p3649_3 (m.d 1 2) (by simp) with h3661 | h3661
                              · linarith only [h0, h3661, hlam]
                              · rcases p3649_3 (m.d 1 3) (by simp) with h3663 | h3663
                                · linarith only [h1, h3663, hlam]
                                · linarith only [h3643, h3663, hlam]
                            · linarith only [h3660, hlam, p3649_0]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h0, hlam, p3649_0]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [hlam, p3649_0]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h3636, hlam, p3649_0]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h3638, hlam, p3649_0]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h3640, hlam, p3649_0]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h1, hlam, p3649_0]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h1, h4, hc12, hc23, hlam, hphi, p3649_1]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [hlam, p3649_0]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h1, h3642, h3648, hc01, hc45, hlam, hphi, ht0b, ht5b, p3649_1]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p3649_1]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h2, hlam, p3649_0]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3649_1]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h3642, hlam, p3649_0]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [hlam, p3649_0]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h1, h3640, h3642, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3649_1]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h3, hlam, p3649_0]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3649_1]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h3643, hlam, p3649_0]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [h3644, hlam, p3649_0]
                          · have p3649_0 := h3649c.1
                            have p3649_1 := h3649c.2.1
                            have p3649_2 := h3649c.2.2.1
                            have p3649_3 := h3649c.2.2.2
                            linarith only [hlam, p3649_0]
                        · rcases h1bigk with h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [hlam, p3687_0]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            rcases p3687_3 (m.d 0 1) (by simp) with h3689 | h3689
                            · rcases p3687_3 (m.d 1 2) (by simp) with h3690 | h3690
                              · linarith only [h3690, hlam, p3687_0]
                              · rcases p3687_3 (m.d 1 3) (by simp) with h3692 | h3692
                                · linarith only [h1, h3692, hlam]
                                · linarith only [h3636, h3692, hlam]
                            · linarith only [h3689, hlam, p3687_0]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [h3642, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3687_1]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [h3644, h3648, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3687_1]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [h3644, h3648, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3687_1]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [h0, hlam, p3687_0]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [hlam, p3687_0]
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
                            linarith only [h3640, hlam, p3687_0]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [h1, hlam, p3687_0]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3687_1]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [hlam, p3687_0]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [h1, h3644, h3648, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3687_1]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p3687_1]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [h2, hlam, p3687_0]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3687_1]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [h3642, hlam, p3687_0]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [hlam, p3687_0]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [h1, h3640, h3642, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3687_1]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [h3, hlam, p3687_0]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3687_1]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [h3643, hlam, p3687_0]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [h3644, hlam, p3687_0]
                          · have p3687_0 := h3687c.1
                            have p3687_1 := h3687c.2.1
                            have p3687_2 := h3687c.2.2.1
                            have p3687_3 := h3687c.2.2.2
                            linarith only [hlam, p3687_0]
                      · linarith only [h3093, h3635, h3647, hlam]
                    · linarith only [h3634, h3646, h4, hlam]
                  · linarith only [h3633, h3645, h4, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3722 | h3722
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3723 | h3723
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3724 | h3724
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3725 | h3725
                        · linarith only [h3642, h3644, h3725, hlam]
                        · rcases h1bigk with h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [hlam, p3727_0]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            rcases p3727_3 (m.d 0 1) (by simp) with h3729 | h3729
                            · rcases p3727_3 (m.d 1 2) (by simp) with h3730 | h3730
                              · linarith only [h3730, hlam, p3727_0]
                              · rcases p3727_3 (m.d 1 3) (by simp) with h3732 | h3732
                                · linarith only [h1, h3732, hlam]
                                · linarith only [h3636, h3732, hlam]
                            · linarith only [h3729, hlam, p3727_0]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [h3642, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3727_1]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            rcases p3727_3 (m.d 0 1) (by simp) with h3737 | h3737
                            · rcases p3727_3 (m.d 1 2) (by simp) with h3738 | h3738
                              · linarith only [h0, h3738, hlam]
                              · rcases p3727_3 (m.d 1 3) (by simp) with h3740 | h3740
                                · linarith only [h1, h3740, hlam]
                                · linarith only [h3642, h3740, hlam]
                            · linarith only [h3737, hlam, p3727_0]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            rcases p3727_3 (m.d 0 1) (by simp) with h3744 | h3744
                            · rcases p3727_3 (m.d 1 2) (by simp) with h3745 | h3745
                              · linarith only [h0, h3745, hlam]
                              · rcases p3727_3 (m.d 1 3) (by simp) with h3747 | h3747
                                · linarith only [h1, h3747, hlam]
                                · linarith only [h3643, h3747, hlam]
                            · linarith only [h3744, hlam, p3727_0]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [h0, hlam, p3727_0]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [hlam, p3727_0]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [h3636, hlam, p3727_0]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [h3638, hlam, p3727_0]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [h3640, hlam, p3727_0]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [h1, hlam, p3727_0]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3727_1]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [hlam, p3727_0]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [h1, h3638, h4, hc12, hc23, hlam, hphi, p3727_1]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p3727_1]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [h2, hlam, p3727_0]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [h3635, h3644, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3727_1]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [h3642, hlam, p3727_0]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [hlam, p3727_0]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [h3644, hlam, p3727_1]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [h3, hlam, p3727_0]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3727_1]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [h3643, hlam, p3727_0]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [h3633, h3635, h3644, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3727_1]
                          · have p3727_0 := h3727c.1
                            have p3727_1 := h3727c.2.1
                            have p3727_2 := h3727c.2.2.1
                            have p3727_3 := h3727c.2.2.2
                            linarith only [hlam, p3727_0]
                      · linarith only [h0, h3093, h3633, h3635, h3724, h4, hc12, hc23, hlam, hphi]
                    · linarith only [h3634, h3723, h4, hlam]
                  · linarith only [h3633, h3722, h4, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3774 | h3774
                · linarith only [h3642, h3643, h3774, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3776 | h3776
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3777 | h3777
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3778 | h3778
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3779 | h3779
                        · linarith only [h3634, h3638, h3642, h3643, h3774, h3779, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h1bigk with h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [hlam, p3781_0]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            rcases p3781_3 (m.d 0 1) (by simp) with h3783 | h3783
                            · rcases p3781_3 (m.d 1 2) (by simp) with h3784 | h3784
                              · linarith only [h3784, hlam, p3781_0]
                              · rcases p3781_3 (m.d 1 3) (by simp) with h3786 | h3786
                                · linarith only [h1, h3786, hlam]
                                · linarith only [h3636, h3786, hlam]
                            · linarith only [h3783, hlam, p3781_0]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h3642, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3781_1]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            rcases p3781_3 (m.d 0 1) (by simp) with h3791 | h3791
                            · rcases p3781_3 (m.d 1 2) (by simp) with h3792 | h3792
                              · linarith only [h0, h3792, hlam]
                              · rcases p3781_3 (m.d 1 3) (by simp) with h3794 | h3794
                                · linarith only [h1, h3794, hlam]
                                · linarith only [h3642, h3794, hlam]
                            · linarith only [h3791, hlam, p3781_0]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h3642, h3643, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3781_1]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h0, hlam, p3781_0]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [hlam, p3781_0]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h3636, hlam, p3781_0]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h3638, hlam, p3781_0]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h3640, hlam, p3781_0]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h1, hlam, p3781_0]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3781_1]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [hlam, p3781_0]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h3, h3422, h3638, h3643, hc12, hc25, hlam, hphi, p3781_1]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h3643, hlam, p3781_1]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h2, hlam, p3781_0]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3781_1]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h3642, hlam, p3781_0]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [hlam, p3781_0]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h3774, hlam, p3781_1]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h3, hlam, p3781_0]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3781_1]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h3633, h3635, h3642, h3643, h3779, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3781_1]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [h3633, h3635, h3643, h3779, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3781_1]
                          · have p3781_0 := h3781c.1
                            have p3781_1 := h3781c.2.1
                            have p3781_2 := h3781c.2.2.1
                            have p3781_3 := h3781c.2.2.2
                            linarith only [hlam, p3781_0]
                      · linarith only [h0, h3093, h3633, h3635, h3778, h4, hc12, hc23, hlam, hphi]
                    · linarith only [h3634, h3777, h4, hlam]
                  · linarith only [h1, h3633, h3635, h3642, h3774, h3776, h4, hc01, hc15, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3822 | h3822
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3823 | h3823
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3824 | h3824
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3825 | h3825
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3826 | h3826
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3827 | h3827
                        · rcases h1bigk with h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c | h3828c
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [hlam, p3828_0]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            rcases p3828_3 (m.d 0 1) (by simp) with h3830 | h3830
                            · rcases p3828_3 (m.d 1 2) (by simp) with h3831 | h3831
                              · linarith only [h3831, hlam, p3828_0]
                              · rcases p3828_3 (m.d 1 3) (by simp) with h3833 | h3833
                                · linarith only [h1, h3833, hlam]
                                · linarith only [h3636, h3833, hlam]
                            · linarith only [h3830, hlam, p3828_0]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h3822, h3827, hc01, hc45, hlam, hphi, ht0b, ht5b, p3828_1]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h3642, h3822, h3827, hc01, hc45, hlam, hphi, ht0b, ht5b, p3828_1]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            rcases p3828_3 (m.d 0 1) (by simp) with h3839 | h3839
                            · rcases p3828_3 (m.d 1 2) (by simp) with h3840 | h3840
                              · linarith only [h0, h3840, hlam]
                              · rcases p3828_3 (m.d 1 3) (by simp) with h3842 | h3842
                                · linarith only [h1, h3842, hlam]
                                · linarith only [h3822, h3842, hlam]
                            · linarith only [h3839, hlam, p3828_0]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h0, hlam, p3828_0]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [hlam, p3828_0]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h3636, hlam, p3828_0]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h3638, hlam, p3828_0]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h3640, hlam, p3828_0]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h1, hlam, p3828_0]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h3633, h3642, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3828_1]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [hlam, p3828_0]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h3642, hlam, p3828_1]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h3633, h3642, h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3828_1]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h2, hlam, p3828_0]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3828_1]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h3633, h3642, h4, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3828_1]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [hlam, p3828_0]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h3633, h3640, h3642, h4, hc12, hc23, hlam, hphi, p3828_1]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h3, hlam, p3828_0]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3828_1]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h3822, hlam, p3828_0]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [h3823, hlam, p3828_0]
                          · have p3828_0 := h3828c.1
                            have p3828_1 := h3828c.2.1
                            have p3828_2 := h3828c.2.2.1
                            have p3828_3 := h3828c.2.2.2
                            linarith only [hlam, p3828_0]
                        · linarith only [h3633, h3635, h3636, h3642, h3827, h4, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h3093, h3633, h3642, h3822, h3823, h3826, h4, hc12, hc23, hlam, hphi]
                    · linarith only [h3633, h3642, h3825, h4, hc13, hc35, hlam, hphi]
                  · linarith only [h3633, h3824, h4, hlam]
                · linarith only [h3642, h3822, h3823, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3871 | h3871
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3872 | h3872
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3873 | h3873
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3874 | h3874
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3875 | h3875
                        · rcases h1bigk with h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c | h3876c
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [hlam, p3876_0]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            rcases p3876_3 (m.d 0 1) (by simp) with h3878 | h3878
                            · rcases p3876_3 (m.d 1 2) (by simp) with h3879 | h3879
                              · linarith only [h3879, hlam, p3876_0]
                              · rcases p3876_3 (m.d 1 3) (by simp) with h3881 | h3881
                                · linarith only [h1, h3881, hlam]
                                · linarith only [h3636, h3881, hlam]
                            · linarith only [h3878, hlam, p3876_0]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            rcases p3876_3 (m.d 0 1) (by simp) with h3885 | h3885
                            · rcases p3876_3 (m.d 1 2) (by simp) with h3886 | h3886
                              · linarith only [h0, h3886, hlam]
                              · rcases p3876_3 (m.d 1 3) (by simp) with h3888 | h3888
                                · linarith only [h3888, hlam, p3876_0]
                                · rcases p3876_3 (m.d 1 4) (by simp) with h3890 | h3890
                                  · linarith only [h2, h3890, hlam]
                                  · linarith only [h3642, h3890, hlam]
                            · linarith only [h3885, hlam, p3876_0]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [h3871, hc01, hc45, hlam, hphi, ht0b, ht5b, p3876_1]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            rcases p3876_3 (m.d 0 1) (by simp) with h3895 | h3895
                            · rcases p3876_3 (m.d 1 2) (by simp) with h3896 | h3896
                              · linarith only [h0, h3896, hlam]
                              · rcases p3876_3 (m.d 1 3) (by simp) with h3898 | h3898
                                · linarith only [h1, h3898, hlam]
                                · rcases p3876_3 (m.d 1 4) (by simp) with h3900 | h3900
                                  · linarith only [h2, h3900, hlam]
                                  · linarith only [h3871, h3900, hlam]
                            · linarith only [h3895, hlam, p3876_0]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [h0, hlam, p3876_0]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [hlam, p3876_0]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [h3636, hlam, p3876_0]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [h3638, hlam, p3876_0]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [h3640, hlam, p3876_0]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [h1, hlam, p3876_0]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [h3634, h3822, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3876_1]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [hlam, p3876_0]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [h3642, hlam, p3876_1]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [h3822, hlam, p3876_1]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [h2, hlam, p3876_0]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3876_1]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [h3633, h3642, h4, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3876_1]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [hlam, p3876_0]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [h3633, h3636, h3642, h3822, h4, hc12, hc23, hlam, hphi, p3876_1]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [h3, hlam, p3876_0]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3876_1]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [h3634, h3636, h3822, h4, hc12, hc23, hlam, hphi, p3876_1]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [h3871, hlam, p3876_0]
                          · have p3876_0 := h3876c.1
                            have p3876_1 := h3876c.2.1
                            have p3876_2 := h3876c.2.2.1
                            have p3876_3 := h3876c.2.2.2
                            linarith only [hlam, p3876_0]
                        · linarith only [h3093, h3635, h3636, h3642, h3872, h3875, hc12, hc23, hlam, hphi]
                      · linarith only [h2, h3093, h3871, h3874, hlam]
                    · linarith only [h3634, h3873, h4, hlam]
                  · linarith only [h3633, h3872, h4, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3928 | h3928
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3929 | h3929
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3930 | h3930
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3931 | h3931
                        · linarith only [h3633, h3638, h3871, h3931, h4, hc12, hc23, hlam, hphi]
                        · linarith only [h3633, h3635, h3636, h3642, h3931, h4, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h3093, h3633, h3635, h3930, h4, hc12, hc23, hlam, hphi]
                    · linarith only [h3634, h3929, h4, hlam]
                  · linarith only [h3633, h3928, h4, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3937 | h3937
      · linarith only [h0, h3937, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3939 | h3939
        · linarith only [h0, h3093, h3939, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3941 | h3941
          · linarith only [h0, h3422, h3941, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3943 | h3943
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3944 | h3944
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3945 | h3945
                · linarith only [h2, h3635, h3945, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3947 | h3947
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3948 | h3948
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3949 | h3949
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3950 | h3950
                        · linarith only [h1, h3635, h3943, h3950, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h1bigk with h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c | h3952c
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [hlam, p3952_0]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            rcases p3952_3 (m.d 0 1) (by simp) with h3954 | h3954
                            · rcases p3952_3 (m.d 1 2) (by simp) with h3955 | h3955
                              · linarith only [h3955, hlam, p3952_0]
                              · rcases p3952_3 (m.d 1 3) (by simp) with h3957 | h3957
                                · linarith only [h1, h3957, hlam]
                                · linarith only [h3937, h3957, hlam]
                            · linarith only [h3954, hlam, p3952_0]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [h3944, hc01, hc35, hlam, hphi, ht0b, ht5b, p3952_1]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            rcases p3952_3 (m.d 0 1) (by simp) with h3962 | h3962
                            · rcases p3952_3 (m.d 1 2) (by simp) with h3963 | h3963
                              · linarith only [h0, h3963, hlam]
                              · rcases p3952_3 (m.d 1 3) (by simp) with h3965 | h3965
                                · linarith only [h1, h3965, hlam]
                                · linarith only [h3943, h3965, hlam]
                            · linarith only [h3962, hlam, p3952_0]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            rcases p3952_3 (m.d 0 1) (by simp) with h3969 | h3969
                            · rcases p3952_3 (m.d 1 2) (by simp) with h3970 | h3970
                              · linarith only [h0, h3970, hlam]
                              · rcases p3952_3 (m.d 1 3) (by simp) with h3972 | h3972
                                · linarith only [h1, h3972, hlam]
                                · linarith only [h3944, h3972, hlam]
                            · linarith only [h3969, hlam, p3952_0]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [h0, hlam, p3952_0]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [hlam, p3952_0]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [h3937, hlam, p3952_0]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [h3939, hlam, p3952_0]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [h3941, hlam, p3952_0]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [h1, hlam, p3952_0]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3952_1]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [hlam, p3952_0]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [h1, h3939, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3952_1]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [h1, h3939, h3945, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3952_1]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [h2, hlam, p3952_0]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3952_1]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [h3943, hlam, p3952_0]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [hlam, p3952_0]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [h3945, hlam, p3952_1]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [h3, hlam, p3952_0]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3952_1]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [h3944, hlam, p3952_0]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [h3, h3635, h3949, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3952_1]
                          · have p3952_0 := h3952c.1
                            have p3952_1 := h3952c.2.1
                            have p3952_2 := h3952c.2.2.1
                            have p3952_3 := h3952c.2.2.2
                            linarith only [hlam, p3952_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3996 | h3996
                        · linarith only [h3093, h3949, h3996, hc02, hc34, hlam, hphi, ht23]
                        · rcases h1bigk with h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [hlam, p3998_0]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            rcases p3998_3 (m.d 0 1) (by simp) with h4000 | h4000
                            · rcases p3998_3 (m.d 1 2) (by simp) with h4001 | h4001
                              · linarith only [h4001, hlam, p3998_0]
                              · rcases p3998_3 (m.d 1 3) (by simp) with h4003 | h4003
                                · linarith only [h1, h4003, hlam]
                                · linarith only [h3937, h4003, hlam]
                            · linarith only [h4000, hlam, p3998_0]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [h3944, hc01, hc35, hlam, hphi, ht0b, ht5b, p3998_1]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            rcases p3998_3 (m.d 0 1) (by simp) with h4008 | h4008
                            · rcases p3998_3 (m.d 1 2) (by simp) with h4009 | h4009
                              · linarith only [h0, h4009, hlam]
                              · rcases p3998_3 (m.d 1 3) (by simp) with h4011 | h4011
                                · linarith only [h1, h4011, hlam]
                                · linarith only [h3943, h4011, hlam]
                            · linarith only [h4008, hlam, p3998_0]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            rcases p3998_3 (m.d 0 1) (by simp) with h4015 | h4015
                            · rcases p3998_3 (m.d 1 2) (by simp) with h4016 | h4016
                              · linarith only [h0, h4016, hlam]
                              · rcases p3998_3 (m.d 1 3) (by simp) with h4018 | h4018
                                · linarith only [h1, h4018, hlam]
                                · linarith only [h3944, h4018, hlam]
                            · linarith only [h4015, hlam, p3998_0]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [h0, hlam, p3998_0]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [hlam, p3998_0]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [h3937, hlam, p3998_0]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [h3939, hlam, p3998_0]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [h3941, hlam, p3998_0]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [h1, hlam, p3998_0]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3998_1]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [hlam, p3998_0]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [h1, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3998_1]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p3998_1]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [h2, hlam, p3998_0]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3998_1]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [h3943, hlam, p3998_0]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [hlam, p3998_0]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [h3945, hlam, p3998_1]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [h3, hlam, p3998_0]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3998_1]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [h3944, hlam, p3998_0]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [h3, h3635, hc14, hc45, hlam, hphi, p3998_1]
                          · have p3998_0 := h3998c.1
                            have p3998_1 := h3998c.2.1
                            have p3998_2 := h3998c.2.2.1
                            have p3998_3 := h3998c.2.2.2
                            linarith only [hlam, p3998_0]
                    · linarith only [h3634, h3948, h4, hlam]
                  · linarith only [h3633, h3947, h4, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4044 | h4044
                · linarith only [h2, h3634, h3635, h3943, h3944, h4044, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4046 | h4046
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4047 | h4047
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4048 | h4048
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4049 | h4049
                        · linarith only [h3634, h3635, h3943, h3944, h4049, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h1bigk with h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c | h4051c
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [hlam, p4051_0]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            rcases p4051_3 (m.d 0 1) (by simp) with h4053 | h4053
                            · rcases p4051_3 (m.d 1 2) (by simp) with h4054 | h4054
                              · linarith only [h4054, hlam, p4051_0]
                              · rcases p4051_3 (m.d 1 3) (by simp) with h4056 | h4056
                                · linarith only [h1, h4056, hlam]
                                · linarith only [h3937, h4056, hlam]
                            · linarith only [h4053, hlam, p4051_0]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h3943, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4051_1]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            rcases p4051_3 (m.d 0 1) (by simp) with h4061 | h4061
                            · rcases p4051_3 (m.d 1 2) (by simp) with h4062 | h4062
                              · linarith only [h0, h4062, hlam]
                              · rcases p4051_3 (m.d 1 3) (by simp) with h4064 | h4064
                                · linarith only [h1, h4064, hlam]
                                · linarith only [h3943, h4064, hlam]
                            · linarith only [h4061, hlam, p4051_0]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h3943, h3944, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4051_1]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h0, hlam, p4051_0]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [hlam, p4051_0]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h3937, hlam, p4051_0]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h3939, hlam, p4051_0]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h3941, hlam, p4051_0]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h1, hlam, p4051_0]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h3634, h3944, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4051_1]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [hlam, p4051_0]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h3634, h3939, h3944, h4, hc12, hc23, hlam, hphi, p4051_1]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h3944, hlam, p4051_1]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h2, hlam, p4051_0]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4051_1]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h3943, hlam, p4051_0]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [hlam, p4051_0]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h4044, hlam, p4051_1]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h3, hlam, p4051_0]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4051_1]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h3634, h3944, h4, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4051_1]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [h3634, h3944, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4051_1]
                          · have p4051_0 := h4051c.1
                            have p4051_1 := h4051c.2.1
                            have p4051_2 := h4051c.2.2.1
                            have p4051_3 := h4051c.2.2.2
                            linarith only [hlam, p4051_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4089 | h4089
                        · linarith only [h1, h3943, h4048, h4089, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h1bigk with h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c | h4091c
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [hlam, p4091_0]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            rcases p4091_3 (m.d 0 1) (by simp) with h4093 | h4093
                            · rcases p4091_3 (m.d 1 2) (by simp) with h4094 | h4094
                              · linarith only [h4094, hlam, p4091_0]
                              · rcases p4091_3 (m.d 1 3) (by simp) with h4096 | h4096
                                · linarith only [h1, h4096, hlam]
                                · linarith only [h3937, h4096, hlam]
                            · linarith only [h4093, hlam, p4091_0]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h3943, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4091_1]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            rcases p4091_3 (m.d 0 1) (by simp) with h4101 | h4101
                            · rcases p4091_3 (m.d 1 2) (by simp) with h4102 | h4102
                              · linarith only [h0, h4102, hlam]
                              · rcases p4091_3 (m.d 1 3) (by simp) with h4104 | h4104
                                · linarith only [h1, h4104, hlam]
                                · linarith only [h3943, h4104, hlam]
                            · linarith only [h4101, hlam, p4091_0]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h3943, h3944, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4091_1]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h0, hlam, p4091_0]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [hlam, p4091_0]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h3937, hlam, p4091_0]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h3939, hlam, p4091_0]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h3941, hlam, p4091_0]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h1, hlam, p4091_0]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4091_1]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [hlam, p4091_0]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h1, h3939, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4091_1]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h3944, hlam, p4091_1]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h2, hlam, p4091_0]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4091_1]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h3943, hlam, p4091_0]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [hlam, p4091_0]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h4044, hlam, p4091_1]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h3, hlam, p4091_0]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4091_1]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h3634, h3944, h4, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4091_1]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [h3634, h3939, h3944, h4, hc12, hc23, hlam, hphi, p4091_1]
                          · have p4091_0 := h4091c.1
                            have p4091_1 := h4091c.2.1
                            have p4091_2 := h4091c.2.2.1
                            have p4091_3 := h4091c.2.2.2
                            linarith only [hlam, p4091_0]
                    · linarith only [h3634, h4, h4047, hlam]
                  · linarith only [h1, h3634, h3943, h3944, h4, h4046, hc01, hc15, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4131 | h4131
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4132 | h4132
                · linarith only [h3633, h3635, h3943, h4131, h4132, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h3943, h4131, h4132, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4135 | h4135
                · linarith only [h2, h3635, h4135, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4137 | h4137
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4138 | h4138
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4139 | h4139
                      · linarith only [h3633, h3635, h3937, h3943, h4139, hc12, hc24, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4141 | h4141
                        · linarith only [h0, h3093, h4139, h4141, hc12, hc34, hlam, hphi, ht23]
                        · rcases h1bigk with h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [hlam, p4143_0]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            rcases p4143_3 (m.d 0 1) (by simp) with h4145 | h4145
                            · rcases p4143_3 (m.d 1 2) (by simp) with h4146 | h4146
                              · linarith only [h4146, hlam, p4143_0]
                              · rcases p4143_3 (m.d 1 3) (by simp) with h4148 | h4148
                                · linarith only [h1, h4148, hlam]
                                · linarith only [h3937, h4148, hlam]
                            · linarith only [h4145, hlam, p4143_0]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            rcases p4143_3 (m.d 0 1) (by simp) with h4152 | h4152
                            · rcases p4143_3 (m.d 1 2) (by simp) with h4153 | h4153
                              · linarith only [h0, h4153, hlam]
                              · rcases p4143_3 (m.d 1 3) (by simp) with h4155 | h4155
                                · linarith only [h4155, hlam, p4143_0]
                                · rcases p4143_3 (m.d 1 4) (by simp) with h4157 | h4157
                                  · linarith only [h2, h4157, hlam]
                                  · linarith only [h3943, h4157, hlam]
                            · linarith only [h4152, hlam, p4143_0]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            rcases p4143_3 (m.d 0 1) (by simp) with h4161 | h4161
                            · rcases p4143_3 (m.d 1 2) (by simp) with h4162 | h4162
                              · linarith only [h0, h4162, hlam]
                              · rcases p4143_3 (m.d 1 3) (by simp) with h4164 | h4164
                                · linarith only [h1, h4164, hlam]
                                · rcases p4143_3 (m.d 1 4) (by simp) with h4166 | h4166
                                  · linarith only [h4166, hlam, p4143_0]
                                  · rcases p4143_3 (m.d 1 5) (by simp) with h4168 | h4168
                                    · linarith only [h3, h4168, hlam]
                                    · linarith only [h4135, h4168, hlam]
                            · linarith only [h4161, hlam, p4143_0]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            rcases p4143_3 (m.d 0 1) (by simp) with h4172 | h4172
                            · rcases p4143_3 (m.d 1 2) (by simp) with h4173 | h4173
                              · linarith only [h0, h4173, hlam]
                              · rcases p4143_3 (m.d 1 3) (by simp) with h4175 | h4175
                                · linarith only [h1, h4175, hlam]
                                · rcases p4143_3 (m.d 1 4) (by simp) with h4177 | h4177
                                  · linarith only [h2, h4177, hlam]
                                  · rcases p4143_3 (m.d 1 5) (by simp) with h4179 | h4179
                                    · linarith only [h4179, hlam, p4143_0]
                                    · rcases h1emin with h4181 | h4181 | h4181 | h4181 | h4181
                                      · rcases h5bigk with h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c | h4182c
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [hlam, p4182_0]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          rcases p4182_3 (m.d 0 5) (by simp) with h4184 | h4184
                                          · rcases p4182_3 (m.d 1 5) (by simp) with h4185 | h4185
                                            · linarith only [h3, h4185, hlam]
                                            · rcases p4182_3 (m.d 2 5) (by simp) with h4187 | h4187
                                              · rcases p4182_3 (m.d 3 5) (by simp) with h4188 | h4188
                                                · linarith only [h3634, h4188, hlam]
                                                · linarith only [h4131, h4188, hlam]
                                              · linarith only [h3941, h4187, hlam]
                                          · linarith only [h3, h4184, hlam]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [h3422, hlam, p4182_0]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [h3422, h4131, h4139, hc13, hc45, hlam, hphi, ht34, p4182_1]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [h3635, hlam, p4182_1]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [h3, hlam, p4182_0]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [hlam, p4182_0]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [h3941, hlam, p4182_0]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [h4131, hlam, p4182_1]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [h4135, hlam, p4182_1]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [h3634, h4131, h4139, hc13, hc45, hlam, hphi, ht34, p4182_1]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          rcases p4182_3 (m.d 0 5) (by simp) with h4202 | h4202
                                          · linarith only [h3422, h4202, hlam]
                                          · linarith only [h3, h4202, hlam]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [hlam, p4182_0]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [h3937, h3943, h4139, h4141, hc12, hc45, hlam, hphi, ht23, ht34, p4182_1]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [h4139, hlam, p4182_1]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [h3634, hlam, p4182_0]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [h3634, h3939, h4, h4135, hc12, hc23, hlam, hphi, p4182_1]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [h4138, hlam, p4182_0]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [hlam, p4182_0]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [h4141, hlam, p4182_1]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [h3633, h3635, h3937, h3943, hc12, hc45, hlam, hphi, ht23, ht34, p4182_1]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          rcases p4182_3 (m.d 0 5) (by simp) with h4214 | h4214
                                          · linarith only [h3635, h4214, hlam]
                                          · linarith only [h3, h4214, hlam]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [h0, h3422, hc12, hc45, hlam, hphi, ht23, ht34, p4182_1]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [h3937, h4131, hc12, hc45, hlam, hphi, ht23, ht34, p4182_1]
                                        · have p4182_0 := h4182c.1
                                          have p4182_1 := h4182c.2.1
                                          have p4182_2 := h4182c.2.2.1
                                          have p4182_3 := h4182c.2.2.2
                                          linarith only [hlam, p4182_0]
                                      · linarith only [h3633, h3937, h3943, h4181, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                      · linarith only [h3633, h3943, h4181, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                      · linarith only [h4135, h4181, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p4143_1]
                                      · linarith only [h4181, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p4143_1]
                            · linarith only [h4172, hlam, p4143_0]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [h0, hlam, p4143_0]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [hlam, p4143_0]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [h3937, hlam, p4143_0]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [h3939, hlam, p4143_0]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [h3941, hlam, p4143_0]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [h1, hlam, p4143_0]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [h1, h3633, h3943, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4143_1]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [hlam, p4143_0]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [h3943, hlam, p4143_1]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [h4131, hlam, p4143_1]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [h2, hlam, p4143_0]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4143_1]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [h3633, h3635, h3943, hc13, hc45, hlam, hphi, ht34, p4143_1]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [hlam, p4143_0]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [h4135, hlam, p4143_1]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [h3, hlam, p4143_0]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4143_1]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [h3634, h3937, h4131, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4143_1]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p4143_1]
                          · have p4143_0 := h4143c.1
                            have p4143_1 := h4143c.2.1
                            have p4143_2 := h4143c.2.2.1
                            have p4143_3 := h4143c.2.2.2
                            linarith only [hlam, p4143_0]
                    · linarith only [h3634, h4, h4138, hlam]
                  · linarith only [h0, h3633, h3635, h4, h4137, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4247 | h4247
    · linarith only [h3633, h3634, h4247, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4249 | h4249
      · linarith only [h0, h4, h4249, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4251 | h4251
        · linarith only [h0, h3093, h4251, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4253 | h4253
          · linarith only [h0, h3422, h4253, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4255 | h4255
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4256 | h4256
              · linarith only [h1, h3634, h4256, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4258 | h4258
                · linarith only [h2, h3633, h3634, h4247, h4258, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4260 | h4260
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4261 | h4261
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4262 | h4262
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4263 | h4263
                        · linarith only [h0, h3093, h3633, h3634, h4247, h4261, h4263, hc12, hc23, hlam, hphi]
                        · rcases h1bigk with h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [hlam, p4265_0]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            rcases p4265_3 (m.d 0 1) (by simp) with h4267 | h4267
                            · rcases p4265_3 (m.d 1 2) (by simp) with h4268 | h4268
                              · linarith only [h4268, hlam, p4265_0]
                              · rcases p4265_3 (m.d 1 3) (by simp) with h4270 | h4270
                                · linarith only [h1, h4270, hlam]
                                · linarith only [h4249, h4270, hlam]
                            · linarith only [h4267, hlam, p4265_0]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h4255, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4265_1]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            rcases p4265_3 (m.d 0 1) (by simp) with h4275 | h4275
                            · rcases p4265_3 (m.d 1 2) (by simp) with h4276 | h4276
                              · linarith only [h0, h4276, hlam]
                              · rcases p4265_3 (m.d 1 3) (by simp) with h4278 | h4278
                                · linarith only [h1, h4278, hlam]
                                · linarith only [h4255, h4278, hlam]
                            · linarith only [h4275, hlam, p4265_0]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h4255, h4256, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4265_1]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h0, hlam, p4265_0]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [hlam, p4265_0]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h4249, hlam, p4265_0]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h4251, hlam, p4265_0]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h4253, hlam, p4265_0]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h1, hlam, p4265_0]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4265_1]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [hlam, p4265_0]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h1, h3634, h4251, h4260, h4262, h4263, hc12, hc23, hlam, hphi, p4265_1]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h4256, hlam, p4265_1]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h2, hlam, p4265_0]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h1, h2, h3634, h4255, h4260, h4262, h4263, hc01, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p4265_1]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h4255, hlam, p4265_0]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [hlam, p4265_0]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h4258, hlam, p4265_1]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h3, hlam, p4265_0]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h1, h3, h3634, h4255, h4260, h4262, h4263, hc01, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p4265_1]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h3, h3634, h4255, h4260, h4262, h4263, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4265_1]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [h3, h3634, h4260, h4262, h4263, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4265_1]
                          · have p4265_0 := h4265c.1
                            have p4265_1 := h4265c.2.1
                            have p4265_2 := h4265c.2.2.1
                            have p4265_3 := h4265c.2.2.2
                            linarith only [hlam, p4265_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4303 | h4303
                        · linarith only [h1, h4255, h4262, h4303, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h1bigk with h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c | h4305c
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [hlam, p4305_0]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            rcases p4305_3 (m.d 0 1) (by simp) with h4307 | h4307
                            · rcases p4305_3 (m.d 1 2) (by simp) with h4308 | h4308
                              · linarith only [h4308, hlam, p4305_0]
                              · rcases p4305_3 (m.d 1 3) (by simp) with h4310 | h4310
                                · linarith only [h1, h4310, hlam]
                                · linarith only [h4249, h4310, hlam]
                            · linarith only [h4307, hlam, p4305_0]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h4255, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4305_1]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            rcases p4305_3 (m.d 0 1) (by simp) with h4315 | h4315
                            · rcases p4305_3 (m.d 1 2) (by simp) with h4316 | h4316
                              · linarith only [h0, h4316, hlam]
                              · rcases p4305_3 (m.d 1 3) (by simp) with h4318 | h4318
                                · linarith only [h1, h4318, hlam]
                                · linarith only [h4255, h4318, hlam]
                            · linarith only [h4315, hlam, p4305_0]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h4255, h4256, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4305_1]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h0, hlam, p4305_0]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [hlam, p4305_0]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h4249, hlam, p4305_0]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h4251, hlam, p4305_0]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h4253, hlam, p4305_0]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h1, hlam, p4305_0]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h1, h3634, h4261, hc12, hc25, hlam, hphi, p4305_1]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [hlam, p4305_0]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h1, h3634, h4251, h4261, hc12, hc25, hlam, hphi, p4305_1]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h4256, hlam, p4305_1]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h2, hlam, p4305_0]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4305_1]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h4255, hlam, p4305_0]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [hlam, p4305_0]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h4258, hlam, p4305_1]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h3, hlam, p4305_0]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4305_1]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4305_1]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p4305_1]
                          · have p4305_0 := h4305c.1
                            have p4305_1 := h4305c.2.1
                            have p4305_2 := h4305c.2.2.1
                            have p4305_3 := h4305c.2.2.2
                            linarith only [hlam, p4305_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4343 | h4343
                      · linarith only [h2, h4247, h4251, h4260, h4261, h4343, hc12, hc35, hlam, hphi, ht23]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4345 | h4345
                        · linarith only [h0, h3093, h4255, h4343, h4345, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h1bigk with h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c | h4347c
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [hlam, p4347_0]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            rcases p4347_3 (m.d 0 1) (by simp) with h4349 | h4349
                            · rcases p4347_3 (m.d 1 2) (by simp) with h4350 | h4350
                              · linarith only [h4350, hlam, p4347_0]
                              · rcases p4347_3 (m.d 1 3) (by simp) with h4352 | h4352
                                · linarith only [h1, h4352, hlam]
                                · linarith only [h4249, h4352, hlam]
                            · linarith only [h4349, hlam, p4347_0]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h4255, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4347_1]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            rcases p4347_3 (m.d 0 1) (by simp) with h4357 | h4357
                            · rcases p4347_3 (m.d 1 2) (by simp) with h4358 | h4358
                              · linarith only [h0, h4358, hlam]
                              · rcases p4347_3 (m.d 1 3) (by simp) with h4360 | h4360
                                · linarith only [h1, h4360, hlam]
                                · linarith only [h4255, h4360, hlam]
                            · linarith only [h4357, hlam, p4347_0]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h4255, h4256, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4347_1]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h0, hlam, p4347_0]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [hlam, p4347_0]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h4249, hlam, p4347_0]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h4251, hlam, p4347_0]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h4253, hlam, p4347_0]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h1, hlam, p4347_0]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4347_1]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [hlam, p4347_0]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h1, h4, h4251, h4261, h4345, hc12, hc45, hlam, hphi, ht23, ht34, p4347_1]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h4256, hlam, p4347_1]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h2, hlam, p4347_0]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4347_1]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h4255, hlam, p4347_0]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [hlam, p4347_0]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h4258, hlam, p4347_1]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h3, hlam, p4347_0]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4347_1]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h3, h3422, h4261, h4345, hc13, hc45, hlam, hphi, ht34, p4347_1]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [h3, h3422, h4261, h4345, hc14, hc45, hlam, hphi, p4347_1]
                          · have p4347_0 := h4347c.1
                            have p4347_1 := h4347c.2.1
                            have p4347_2 := h4347c.2.2.1
                            have p4347_3 := h4347c.2.2.2
                            linarith only [hlam, p4347_0]
                  · linarith only [h1, h3634, h4255, h4260, hc23, hc35, hlam, hphi]
            · linarith only [h3633, h3634, h4249, h4255, hc12, hc35, hlam, hphi, ht23]

end R2N4
