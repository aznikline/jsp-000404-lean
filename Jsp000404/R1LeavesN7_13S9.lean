import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7524000 in
set_option maxHeartbeats 7524000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7870 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8661 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8662 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8663 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8664 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8665 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8666 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h8667 | h8667
  · rcases m.htr 1 2 4 (by decide) (by decide) with h8668 | h8668
    · rcases m.htr 1 2 5 (by decide) (by decide) with h8669 | h8669
      · rcases m.htr 1 3 4 (by decide) (by decide) with h8670 | h8670
        · rcases m.htr 1 3 5 (by decide) (by decide) with h8671 | h8671
          · rcases m.htr 1 4 5 (by decide) (by decide) with h8672 | h8672
            · rcases m.htr 2 3 4 (by decide) (by decide) with h8673 | h8673
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8674 | h8674
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8675 | h8675
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8676 | h8676
                    · rcases h2bigk with h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c | h8677c
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [hlam, p8677_0]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h0, hlam, p8677_0]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h8673, h8676, hc02, hc45, hlam, hphi, ht0b, ht5b, p8677_1]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h0, h8673, h8676, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8677_1]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        rcases p8677_3 (m.d 0 2) (by simp) with h8682 | h8682
                        · rcases p8677_3 (m.d 1 2) (by simp) with h8683 | h8683
                          · rcases p8677_3 (m.d 2 3) (by simp) with h8684 | h8684
                            · linarith only [h8661, h8684, hlam]
                            · linarith only [h8674, h8684, hlam]
                          · linarith only [h8669, h8683, hlam]
                        · linarith only [h8682, hlam, p8677_0]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p8677_1]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [hlam, p8677_0]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h8673, h8676, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8677_1]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h8673, h8676, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8677_1]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        rcases p8677_3 (m.d 0 2) (by simp) with h8693 | h8693
                        · linarith only [h0, h8693, hlam]
                        · linarith only [h8663, h8693, hlam]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h8661, hlam, p8677_0]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h8667, hlam, p8677_0]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [hlam, p8677_0]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h8661, h8673, h8676, hc02, hc45, hlam, hphi, ht0b, ht5b, p8677_1]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h0, h8661, h8674, h8676, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8677_1]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h8662, hlam, p8677_0]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h8668, hlam, p8677_0]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h8673, hlam, p8677_0]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [hlam, p8677_0]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h0, h8662, h8674, h8676, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8677_1]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h8663, hlam, p8677_0]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h8669, hlam, p8677_0]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h8674, hlam, p8677_0]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [h8675, hlam, p8677_1]
                      · have p8677_0 := h8677c.1
                        have p8677_1 := h8677c.2.1
                        have p8677_2 := h8677c.2.2.1
                        have p8677_3 := h8677c.2.2.2
                        linarith only [hlam, p8677_0]
                    · rcases h2bigk with h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c | h8711c
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [hlam, p8711_0]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h0, hlam, p8711_0]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h0, h8673, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8711_1]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h0, h8675, h8676, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8711_1]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h0, h8675, h8676, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8711_1]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p8711_1]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [hlam, p8711_0]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h8674, h8675, h8676, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8711_1]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h8675, h8676, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8711_1]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h8675, h8676, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8711_1]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h8661, hlam, p8711_0]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h8667, hlam, p8711_0]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [hlam, p8711_0]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h8675, h8676, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8711_1]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h0, h8661, h8675, h8676, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8711_1]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h8662, hlam, p8711_0]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h8668, hlam, p8711_0]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h8673, hlam, p8711_0]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [hlam, p8711_0]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h8662, h8675, h8676, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p8711_1]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h8663, hlam, p8711_0]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h8669, hlam, p8711_0]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h8674, hlam, p8711_0]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [h8675, hlam, p8711_1]
                      · have p8711_0 := h8711c.1
                        have p8711_1 := h8711c.2.1
                        have p8711_2 := h8711c.2.2.1
                        have p8711_3 := h8711c.2.2.2
                        linarith only [hlam, p8711_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8737 | h8737
                    · linarith only [h8673, h8675, h8737, hlam]
                    · rcases h2bigk with h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c | h8739c
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [hlam, p8739_0]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [h0, hlam, p8739_0]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [h0, h8673, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8739_1]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        rcases p8739_3 (m.d 0 2) (by simp) with h8743 | h8743
                        · rcases p8739_3 (m.d 1 2) (by simp) with h8744 | h8744
                          · rcases p8739_3 (m.d 2 3) (by simp) with h8745 | h8745
                            · linarith only [h8661, h8745, hlam]
                            · linarith only [h8673, h8745, hlam]
                          · linarith only [h8668, h8744, hlam]
                        · linarith only [h8743, hlam, p8739_0]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        rcases p8739_3 (m.d 0 2) (by simp) with h8750 | h8750
                        · rcases p8739_3 (m.d 1 2) (by simp) with h8751 | h8751
                          · rcases p8739_3 (m.d 2 3) (by simp) with h8752 | h8752
                            · linarith only [h8661, h8752, hlam]
                            · linarith only [h8674, h8752, hlam]
                          · linarith only [h8669, h8751, hlam]
                        · linarith only [h8750, hlam, p8739_0]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p8739_1]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [hlam, p8739_0]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [h8674, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8739_1]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        rcases p8739_3 (m.d 0 2) (by simp) with h8760 | h8760
                        · linarith only [h0, h8760, hlam]
                        · linarith only [h8662, h8760, hlam]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        rcases p8739_3 (m.d 0 2) (by simp) with h8763 | h8763
                        · linarith only [h0, h8763, hlam]
                        · linarith only [h8663, h8763, hlam]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [h8661, hlam, p8739_0]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [h8667, hlam, p8739_0]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [hlam, p8739_0]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [h8661, h8673, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p8739_1]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [h0, h8661, h8673, h8675, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8739_1]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [h8662, hlam, p8739_0]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [h8668, hlam, p8739_0]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [h8673, hlam, p8739_0]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [hlam, p8739_0]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [h8675, hlam, p8739_0]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [h8663, hlam, p8739_0]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [h8669, hlam, p8739_0]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [h8674, hlam, p8739_0]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [h0, h8663, h8673, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8739_1]
                      · have p8739_0 := h8739c.1
                        have p8739_1 := h8739c.2.1
                        have p8739_2 := h8739c.2.2.1
                        have p8739_3 := h8739c.2.2.2
                        linarith only [hlam, p8739_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8781 | h8781
                  · linarith only [h8673, h8674, h8781, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8783 | h8783
                    · linarith only [h0, h8661, h8673, h8781, h8783, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases h2bigk with h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c | h8785c
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [hlam, p8785_0]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h0, hlam, p8785_0]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h0, h8673, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8785_1]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        rcases p8785_3 (m.d 0 2) (by simp) with h8789 | h8789
                        · rcases p8785_3 (m.d 1 2) (by simp) with h8790 | h8790
                          · rcases p8785_3 (m.d 2 3) (by simp) with h8791 | h8791
                            · linarith only [h8661, h8791, hlam]
                            · linarith only [h8673, h8791, hlam]
                          · linarith only [h8668, h8790, hlam]
                        · linarith only [h8789, hlam, p8785_0]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h0, h8673, h8674, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8785_1]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p8785_1]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [hlam, p8785_0]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h8673, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8785_1]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        rcases p8785_3 (m.d 0 2) (by simp) with h8800 | h8800
                        · linarith only [h0, h8800, hlam]
                        · linarith only [h8662, h8800, hlam]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h8673, h8674, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8785_1]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h8661, hlam, p8785_0]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h8667, hlam, p8785_0]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [hlam, p8785_0]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h8661, h8673, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p8785_1]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h8674, hlam, p8785_1]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h8662, hlam, p8785_0]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h8668, hlam, p8785_0]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h8673, hlam, p8785_0]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [hlam, p8785_0]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h8781, hlam, p8785_0]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h8663, hlam, p8785_0]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h8669, hlam, p8785_0]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h0, h8663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8785_1]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [h6923, h8666, h8667, h8670, h8673, h8674, h8783, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8785_1]
                      · have p8785_0 := h8785c.1
                        have p8785_1 := h8785c.2.1
                        have p8785_2 := h8785c.2.2.1
                        have p8785_3 := h8785c.2.2.2
                        linarith only [hlam, p8785_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8819 | h8819
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8820 | h8820
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8821 | h8821
                    · rcases h2bigk with h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [hlam, p8822_0]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h0, hlam, p8822_0]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h0, h8819, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8822_1]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h0, h8673, h8819, h8821, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8822_1]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        rcases p8822_3 (m.d 0 2) (by simp) with h8827 | h8827
                        · rcases p8822_3 (m.d 1 2) (by simp) with h8828 | h8828
                          · rcases p8822_3 (m.d 2 3) (by simp) with h8829 | h8829
                            · linarith only [h8661, h8829, hlam]
                            · linarith only [h8819, h8829, hlam]
                          · linarith only [h8669, h8828, hlam]
                        · linarith only [h8827, hlam, p8822_0]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p8822_1]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [hlam, p8822_0]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h8819, h8821, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8822_1]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h8673, h8819, h8821, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8822_1]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        rcases p8822_3 (m.d 0 2) (by simp) with h8838 | h8838
                        · linarith only [h0, h8838, hlam]
                        · linarith only [h8663, h8838, hlam]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h8661, hlam, p8822_0]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h8667, hlam, p8822_0]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [hlam, p8822_0]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h8673, hlam, p8822_1]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h8661, h8819, h8821, hc02, hc45, hlam, hphi, ht0b, ht5b, p8822_1]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h8662, hlam, p8822_0]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h8668, hlam, p8822_0]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h0, h8662, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8822_1]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [hlam, p8822_0]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h5135, h8664, h8667, h8673, h8819, h8821, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8822_1]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h8663, hlam, p8822_0]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h8669, hlam, p8822_0]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h8819, hlam, p8822_0]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [h8820, hlam, p8822_1]
                      · have p8822_0 := h8822c.1
                        have p8822_1 := h8822c.2.1
                        have p8822_2 := h8822c.2.2.1
                        have p8822_3 := h8822c.2.2.2
                        linarith only [hlam, p8822_0]
                    · linarith only [h6923, h8666, h8667, h8670, h8673, h8819, h8821, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h8673, h8819, h8820, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8858 | h8858
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8859 | h8859
                    · rcases h2bigk with h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c | h8860c
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [hlam, p8860_0]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [h0, hlam, p8860_0]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        rcases p8860_3 (m.d 0 2) (by simp) with h8863 | h8863
                        · rcases p8860_3 (m.d 1 2) (by simp) with h8864 | h8864
                          · rcases p8860_3 (m.d 2 3) (by simp) with h8865 | h8865
                            · linarith only [h8865, hlam, p8860_0]
                            · rcases p8860_3 (m.d 2 4) (by simp) with h8867 | h8867
                              · linarith only [h8662, h8867, hlam]
                              · linarith only [h8673, h8867, hlam]
                          · linarith only [h8667, h8864, hlam]
                        · linarith only [h8863, hlam, p8860_0]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [h0, h8858, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8860_1]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        rcases p8860_3 (m.d 0 2) (by simp) with h8873 | h8873
                        · rcases p8860_3 (m.d 1 2) (by simp) with h8874 | h8874
                          · rcases p8860_3 (m.d 2 3) (by simp) with h8875 | h8875
                            · linarith only [h8661, h8875, hlam]
                            · rcases p8860_3 (m.d 2 4) (by simp) with h8877 | h8877
                              · linarith only [h8662, h8877, hlam]
                              · linarith only [h8858, h8877, hlam]
                          · linarith only [h8669, h8874, hlam]
                        · linarith only [h8873, hlam, p8860_0]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p8860_1]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [hlam, p8860_0]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        rcases p8860_3 (m.d 0 2) (by simp) with h8884 | h8884
                        · linarith only [h0, h8884, hlam]
                        · linarith only [h8661, h8884, hlam]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [h8858, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8860_1]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        rcases p8860_3 (m.d 0 2) (by simp) with h8888 | h8888
                        · linarith only [h0, h8888, hlam]
                        · linarith only [h8663, h8888, hlam]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [h8661, hlam, p8860_0]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [h8667, hlam, p8860_0]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [hlam, p8860_0]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [h8673, hlam, p8860_1]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [h8819, hlam, p8860_1]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [h8662, hlam, p8860_0]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [h8668, hlam, p8860_0]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [h8662, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8860_1]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [hlam, p8860_0]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [h5135, h8664, h8667, h8673, h8819, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8860_1]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [h8663, hlam, p8860_0]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [h8669, hlam, p8860_0]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [h0, h8663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8860_1]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [h8858, hlam, p8860_1]
                      · have p8860_0 := h8860c.1
                        have p8860_1 := h8860c.2.1
                        have p8860_2 := h8860c.2.2.1
                        have p8860_3 := h8860c.2.2.2
                        linarith only [hlam, p8860_0]
                    · linarith only [h8673, h8858, h8859, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8907 | h8907
                    · rcases h2bigk with h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c | h8908c
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [hlam, p8908_0]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [h0, hlam, p8908_0]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        rcases p8908_3 (m.d 0 2) (by simp) with h8911 | h8911
                        · rcases p8908_3 (m.d 1 2) (by simp) with h8912 | h8912
                          · rcases p8908_3 (m.d 2 3) (by simp) with h8913 | h8913
                            · linarith only [h8913, hlam, p8908_0]
                            · rcases p8908_3 (m.d 2 4) (by simp) with h8915 | h8915
                              · linarith only [h8662, h8915, hlam]
                              · linarith only [h8673, h8915, hlam]
                          · linarith only [h8667, h8912, hlam]
                        · linarith only [h8911, hlam, p8908_0]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        rcases p8908_3 (m.d 0 2) (by simp) with h8920 | h8920
                        · rcases p8908_3 (m.d 1 2) (by simp) with h8921 | h8921
                          · rcases p8908_3 (m.d 2 3) (by simp) with h8922 | h8922
                            · linarith only [h8661, h8922, hlam]
                            · rcases p8908_3 (m.d 2 4) (by simp) with h8924 | h8924
                              · linarith only [h8924, hlam, p8908_0]
                              · rcases p8908_3 (m.d 2 5) (by simp) with h8926 | h8926
                                · linarith only [h8663, h8926, hlam]
                                · linarith only [h8858, h8926, hlam]
                          · linarith only [h8668, h8921, hlam]
                        · linarith only [h8920, hlam, p8908_0]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        rcases p8908_3 (m.d 0 2) (by simp) with h8931 | h8931
                        · rcases p8908_3 (m.d 1 2) (by simp) with h8932 | h8932
                          · rcases p8908_3 (m.d 2 3) (by simp) with h8933 | h8933
                            · linarith only [h8661, h8933, hlam]
                            · rcases p8908_3 (m.d 2 4) (by simp) with h8935 | h8935
                              · linarith only [h8662, h8935, hlam]
                              · rcases p8908_3 (m.d 2 5) (by simp) with h8937 | h8937
                                · linarith only [h8937, hlam, p8908_0]
                                · rcases h3bigk with h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c | h8939c
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [hlam, p8939_0]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [h5135, hlam, p8939_1]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [h8664, h8673, h8858, h8907, hlam, p8939_2]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [h5135, h8667, h8858, h8907, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8939_1]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    rcases p8939_3 (m.d 0 3) (by simp) with h8944 | h8944
                                    · rcases p8939_3 (m.d 1 3) (by simp) with h8945 | h8945
                                      · rcases p8939_3 (m.d 2 3) (by simp) with h8946 | h8946
                                        · linarith only [h8661, h8946, hlam]
                                        · rcases p8939_3 (m.d 3 4) (by simp) with h8948 | h8948
                                          · linarith only [h8664, h8948, hlam]
                                          · linarith only [h8907, h8948, hlam]
                                      · linarith only [h8671, h8945, hlam]
                                    · linarith only [h8944, hlam, p8939_0]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [h8664, h8667, h8673, h8858, h8907, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8939_1]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [hlam, p8939_0]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [h5135, h8664, h8673, h8858, h8907, hlam, p8939_2]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [h8673, h8858, h8907, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8939_1]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    rcases p8939_3 (m.d 0 3) (by simp) with h8957 | h8957
                                    · linarith only [h5135, h8957, hlam]
                                    · linarith only [h8665, h8957, hlam]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [h8661, hlam, p8939_1]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [h8667, hlam, p8939_1]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [hlam, p8939_0]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [h8673, hlam, p8939_0]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [h8819, hlam, p8939_0]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [h8664, hlam, p8939_0]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [h8670, hlam, p8939_0]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    rcases p8939_3 (m.d 0 3) (by simp) with h8967 | h8967
                                    · rcases p8939_3 (m.d 1 3) (by simp) with h8968 | h8968
                                      · rcases p8939_3 (m.d 2 3) (by simp) with h8969 | h8969
                                        · linarith only [h8969, hlam, p8939_0]
                                        · rcases p8939_3 (m.d 3 4) (by simp) with h8971 | h8971
                                          · rcases p8939_3 (m.d 3 5) (by simp) with h8972 | h8972
                                            · linarith only [h8907, h8972, hlam]
                                            · linarith only [h8819, h8972, hlam]
                                          · linarith only [h8971, hlam, p8939_0]
                                      · linarith only [h8667, h8968, hlam]
                                    · linarith only [h8661, h8967, hlam]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [hlam, p8939_0]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [h8664, h8673, h8858, h8907, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8939_1]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [h8665, hlam, p8939_0]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [h8671, hlam, p8939_0]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    rcases p8939_3 (m.d 0 3) (by simp) with h8982 | h8982
                                    · rcases p8939_3 (m.d 1 3) (by simp) with h8983 | h8983
                                      · rcases p8939_3 (m.d 2 3) (by simp) with h8984 | h8984
                                        · linarith only [h8984, hlam, p8939_0]
                                        · rcases p8939_3 (m.d 3 4) (by simp) with h8986 | h8986
                                          · rcases p8939_3 (m.d 3 5) (by simp) with h8987 | h8987
                                            · rcases h5bigk with h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c | h8988c
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [hlam, p8988_0]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h7870, hlam, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                rcases p8988_3 (m.d 0 5) (by simp) with h8991 | h8991
                                                · rcases p8988_3 (m.d 1 5) (by simp) with h8992 | h8992
                                                  · rcases p8988_3 (m.d 2 5) (by simp) with h8993 | h8993
                                                    · linarith only [h8663, h8993, hlam]
                                                    · rcases p8988_3 (m.d 3 5) (by simp) with h8995 | h8995
                                                      · linarith only [h8665, h8995, hlam]
                                                      · linarith only [h8819, h8995, hlam]
                                                  · linarith only [h8669, h8992, hlam]
                                                · linarith only [h8663, h8991, hlam]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8939_1, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                rcases p8988_3 (m.d 0 5) (by simp) with h9001 | h9001
                                                · rcases p8988_3 (m.d 1 5) (by simp) with h9002 | h9002
                                                  · rcases p8988_3 (m.d 2 5) (by simp) with h9003 | h9003
                                                    · linarith only [h8663, h9003, hlam]
                                                    · rcases p8988_3 (m.d 3 5) (by simp) with h9005 | h9005
                                                      · linarith only [h8665, h9005, hlam]
                                                      · linarith only [h8907, h9005, hlam]
                                                  · linarith only [h8672, h9002, hlam]
                                                · linarith only [h8666, h9001, hlam]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8665, h8667, h8670, h8672, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8939_1, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [hlam, p8988_0]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                rcases p8988_3 (m.d 0 5) (by simp) with h9012 | h9012
                                                · linarith only [h7870, h9012, hlam]
                                                · linarith only [h8663, h9012, hlam]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8667, h8670, h8672, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8939_1, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                rcases p8988_3 (m.d 0 5) (by simp) with h9016 | h9016
                                                · linarith only [h7870, h9016, hlam]
                                                · linarith only [h8666, h9016, hlam]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8663, hlam, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8669, hlam, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [hlam, p8988_0]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8819, hlam, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8858, hlam, p8988_0]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8665, hlam, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8671, hlam, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                rcases p8988_3 (m.d 0 5) (by simp) with h9026 | h9026
                                                · rcases p8988_3 (m.d 1 5) (by simp) with h9027 | h9027
                                                  · rcases p8988_3 (m.d 2 5) (by simp) with h9028 | h9028
                                                    · linarith only [h8819, h9028, hlam]
                                                    · rcases p8988_3 (m.d 3 5) (by simp) with h9030 | h9030
                                                      · rcases p8988_3 (m.d 4 5) (by simp) with h9031 | h9031
                                                        · linarith only [h8907, h9031, hlam]
                                                        · linarith only [h8858, h9031, hlam]
                                                      · linarith only [h8819, h9030, hlam]
                                                  · linarith only [h8669, h9027, hlam]
                                                · linarith only [h8663, h9026, hlam]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [hlam, p8988_0]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8673, h8858, hc23, hc35, hlam, hphi, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8666, hlam, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8672, hlam, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h5135, h8664, h8667, h8673, h8858, h8907, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8907, hlam, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [hlam, p8988_0]
                                            · linarith only [h8987, hlam, p8939_0]
                                          · linarith only [h8673, h8986, hlam]
                                      · linarith only [h8667, h8983, hlam]
                                    · linarith only [h8661, h8982, hlam]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [h8907, hlam, p8939_1]
                                  · have p8939_0 := h8939c.1
                                    have p8939_1 := h8939c.2.1
                                    have p8939_2 := h8939c.2.2.1
                                    have p8939_3 := h8939c.2.2.2
                                    linarith only [hlam, p8939_0]
                          · linarith only [h8669, h8932, hlam]
                        · linarith only [h8931, hlam, p8908_0]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p8908_1]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [hlam, p8908_0]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        rcases p8908_3 (m.d 0 2) (by simp) with h9054 | h9054
                        · linarith only [h0, h9054, hlam]
                        · linarith only [h8661, h9054, hlam]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        rcases p8908_3 (m.d 0 2) (by simp) with h9057 | h9057
                        · linarith only [h0, h9057, hlam]
                        · linarith only [h8662, h9057, hlam]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        rcases p8908_3 (m.d 0 2) (by simp) with h9060 | h9060
                        · linarith only [h0, h9060, hlam]
                        · linarith only [h8663, h9060, hlam]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [h8661, hlam, p8908_0]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [h8667, hlam, p8908_0]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [hlam, p8908_0]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [h8673, hlam, p8908_1]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [h8819, hlam, p8908_1]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [h8662, hlam, p8908_0]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [h8668, hlam, p8908_0]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [h8662, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8908_1]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [hlam, p8908_0]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [h8858, hlam, p8908_0]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [h8663, hlam, p8908_0]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [h8669, hlam, p8908_0]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [h5135, h8664, h8667, h8819, h8907, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8908_1]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [h5135, h8664, h8667, h8858, h8907, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8908_1]
                      · have p8908_0 := h8908c.1
                        have p8908_1 := h8908c.2.1
                        have p8908_2 := h8908c.2.2.1
                        have p8908_3 := h8908c.2.2.2
                        linarith only [hlam, p8908_0]
                    · rcases h2bigk with h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c | h9078c
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h0, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        rcases p9078_3 (m.d 0 2) (by simp) with h9081 | h9081
                        · rcases p9078_3 (m.d 1 2) (by simp) with h9082 | h9082
                          · rcases p9078_3 (m.d 2 3) (by simp) with h9083 | h9083
                            · linarith only [h9083, hlam, p9078_0]
                            · rcases p9078_3 (m.d 2 4) (by simp) with h9085 | h9085
                              · linarith only [h8662, h9085, hlam]
                              · linarith only [h8673, h9085, hlam]
                          · linarith only [h8667, h9082, hlam]
                        · linarith only [h9081, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        rcases p9078_3 (m.d 0 2) (by simp) with h9090 | h9090
                        · rcases p9078_3 (m.d 1 2) (by simp) with h9091 | h9091
                          · rcases p9078_3 (m.d 2 3) (by simp) with h9092 | h9092
                            · linarith only [h8661, h9092, hlam]
                            · rcases p9078_3 (m.d 2 4) (by simp) with h9094 | h9094
                              · linarith only [h9094, hlam, p9078_0]
                              · rcases p9078_3 (m.d 2 5) (by simp) with h9096 | h9096
                                · linarith only [h8663, h9096, hlam]
                                · linarith only [h8858, h9096, hlam]
                          · linarith only [h8668, h9091, hlam]
                        · linarith only [h9090, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        rcases p9078_3 (m.d 0 2) (by simp) with h9101 | h9101
                        · rcases p9078_3 (m.d 1 2) (by simp) with h9102 | h9102
                          · rcases p9078_3 (m.d 2 3) (by simp) with h9103 | h9103
                            · linarith only [h8661, h9103, hlam]
                            · rcases p9078_3 (m.d 2 4) (by simp) with h9105 | h9105
                              · linarith only [h8662, h9105, hlam]
                              · rcases p9078_3 (m.d 2 5) (by simp) with h9107 | h9107
                                · linarith only [h9107, hlam, p9078_0]
                                · rcases h3bigk with h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c | h9109c
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [hlam, p9109_0]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [h5135, hlam, p9109_1]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [h8664, h8666, h8673, h8907, hlam, p9109_2]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    rcases p9109_3 (m.d 0 3) (by simp) with h9113 | h9113
                                    · rcases p9109_3 (m.d 1 3) (by simp) with h9114 | h9114
                                      · rcases p9109_3 (m.d 2 3) (by simp) with h9115 | h9115
                                        · linarith only [h8661, h9115, hlam]
                                        · rcases p9109_3 (m.d 3 4) (by simp) with h9117 | h9117
                                          · linarith only [h9117, hlam, p9109_0]
                                          · rcases p9109_3 (m.d 3 5) (by simp) with h9119 | h9119
                                            · linarith only [h8665, h9119, hlam]
                                            · linarith only [h8907, h9119, hlam]
                                      · linarith only [h8670, h9114, hlam]
                                    · linarith only [h9113, hlam, p9109_0]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    rcases p9109_3 (m.d 0 3) (by simp) with h9124 | h9124
                                    · rcases p9109_3 (m.d 1 3) (by simp) with h9125 | h9125
                                      · rcases p9109_3 (m.d 2 3) (by simp) with h9126 | h9126
                                        · linarith only [h8661, h9126, hlam]
                                        · rcases p9109_3 (m.d 3 4) (by simp) with h9128 | h9128
                                          · linarith only [h8664, h9128, hlam]
                                          · rcases p9109_3 (m.d 3 5) (by simp) with h9130 | h9130
                                            · linarith only [h9130, hlam, p9109_0]
                                            · rcases h5bigk with h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c | h9132c
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [hlam, p9132_0]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [h7870, hlam, p9132_1]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                rcases p9132_3 (m.d 0 5) (by simp) with h9135 | h9135
                                                · rcases p9132_3 (m.d 1 5) (by simp) with h9136 | h9136
                                                  · rcases p9132_3 (m.d 2 5) (by simp) with h9137 | h9137
                                                    · linarith only [h8663, h9137, hlam]
                                                    · rcases p9132_3 (m.d 3 5) (by simp) with h9139 | h9139
                                                      · linarith only [h8665, h9139, hlam]
                                                      · linarith only [h8819, h9139, hlam]
                                                  · linarith only [h8669, h9136, hlam]
                                                · linarith only [h8663, h9135, hlam]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                rcases p9132_3 (m.d 0 5) (by simp) with h9144 | h9144
                                                · rcases p9132_3 (m.d 1 5) (by simp) with h9145 | h9145
                                                  · rcases p9132_3 (m.d 2 5) (by simp) with h9146 | h9146
                                                    · linarith only [h8663, h9146, hlam]
                                                    · rcases p9132_3 (m.d 3 5) (by simp) with h9148 | h9148
                                                      · linarith only [h8665, h9148, hlam]
                                                      · rcases p9132_3 (m.d 4 5) (by simp) with h9150 | h9150
                                                        · linarith only [h8666, h9150, hlam]
                                                        · linarith only [h8907, h9150, hlam]
                                                  · linarith only [h8671, h9145, hlam]
                                                · linarith only [h8665, h9144, hlam]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [h7870, h8667, h8670, h8672, h8673, h8907, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9132_1]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [h8666, h8667, h8670, h8672, h8673, h8907, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9132_1]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [hlam, p9132_0]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                rcases p9132_3 (m.d 0 5) (by simp) with h9158 | h9158
                                                · linarith only [h7870, h9158, hlam]
                                                · linarith only [h8663, h9158, hlam]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                rcases p9132_3 (m.d 0 5) (by simp) with h9161 | h9161
                                                · linarith only [h7870, h9161, hlam]
                                                · linarith only [h8665, h9161, hlam]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [h8667, h8670, h8672, h8673, h8907, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9132_1]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [h8663, hlam, p9132_1]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [h8669, hlam, p9132_1]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [hlam, p9132_0]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [h8819, hlam, p9132_1]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [h8858, hlam, p9132_0]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [h8665, hlam, p9132_1]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [h8671, hlam, p9132_1]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [h8858, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p9109_1, p9132_1]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [hlam, p9132_0]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [h8907, hlam, p9132_0]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [h8666, hlam, p9132_1]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [h8672, hlam, p9132_1]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                rcases p9132_3 (m.d 0 5) (by simp) with h9177 | h9177
                                                · rcases p9132_3 (m.d 1 5) (by simp) with h9178 | h9178
                                                  · rcases p9132_3 (m.d 2 5) (by simp) with h9179 | h9179
                                                    · linarith only [h8858, h9179, hlam]
                                                    · rcases p9132_3 (m.d 3 5) (by simp) with h9181 | h9181
                                                      · linarith only [h8907, h9181, hlam]
                                                      · linarith only [h8819, h9181, hlam]
                                                  · linarith only [h8669, h9178, hlam]
                                                · linarith only [h8663, h9177, hlam]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [h8664, h8666, hlam, p9109_2, p9132_1]
                                              · have p9132_0 := h9132c.1
                                                have p9132_1 := h9132c.2.1
                                                have p9132_2 := h9132c.2.2.1
                                                have p9132_3 := h9132c.2.2.2
                                                linarith only [hlam, p9132_0]
                                      · linarith only [h8671, h9125, hlam]
                                    · linarith only [h9124, hlam, p9109_0]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [h8664, h8667, h8673, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9109_1]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [hlam, p9109_0]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [h5135, h8664, h8666, h8673, h8907, hlam, p9109_2]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    rcases p9109_3 (m.d 0 3) (by simp) with h9193 | h9193
                                    · linarith only [h5135, h9193, hlam]
                                    · linarith only [h8664, h9193, hlam]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    rcases p9109_3 (m.d 0 3) (by simp) with h9196 | h9196
                                    · linarith only [h5135, h9196, hlam]
                                    · linarith only [h8665, h9196, hlam]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [h8661, hlam, p9109_1]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [h8667, hlam, p9109_1]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [hlam, p9109_0]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [h8673, hlam, p9109_0]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [h8819, hlam, p9109_0]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [h8664, hlam, p9109_0]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [h8670, hlam, p9109_0]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [h8664, h8666, h8907, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9109_1]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [hlam, p9109_0]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [h8907, hlam, p9109_0]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [h8665, hlam, p9109_0]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [h8671, hlam, p9109_0]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    rcases p9109_3 (m.d 0 3) (by simp) with h9211 | h9211
                                    · rcases p9109_3 (m.d 1 3) (by simp) with h9212 | h9212
                                      · rcases p9109_3 (m.d 2 3) (by simp) with h9213 | h9213
                                        · linarith only [h9213, hlam, p9109_0]
                                        · rcases p9109_3 (m.d 3 4) (by simp) with h9215 | h9215
                                          · linarith only [h8907, h9215, hlam]
                                          · linarith only [h8673, h9215, hlam]
                                      · linarith only [h8667, h9212, hlam]
                                    · linarith only [h8661, h9211, hlam]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [h0, h8661, h8665, h8673, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9109_1]
                                  · have p9109_0 := h9109c.1
                                    have p9109_1 := h9109c.2.1
                                    have p9109_2 := h9109c.2.2.1
                                    have p9109_3 := h9109c.2.2.2
                                    linarith only [hlam, p9109_0]
                          · linarith only [h8669, h9102, hlam]
                        · linarith only [h9101, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h8661, h8665, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p9078_1]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        rcases p9078_3 (m.d 0 2) (by simp) with h9226 | h9226
                        · linarith only [h0, h9226, hlam]
                        · linarith only [h8661, h9226, hlam]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        rcases p9078_3 (m.d 0 2) (by simp) with h9229 | h9229
                        · linarith only [h0, h9229, hlam]
                        · linarith only [h8662, h9229, hlam]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        rcases p9078_3 (m.d 0 2) (by simp) with h9232 | h9232
                        · linarith only [h0, h9232, hlam]
                        · linarith only [h8663, h9232, hlam]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h8661, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h8667, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h8673, hlam, p9078_1]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h8819, hlam, p9078_1]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h8662, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h8668, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h8662, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9078_1]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h8858, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h8663, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h8669, hlam, p9078_0]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h5135, h8665, h8667, h8819, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9078_1]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [h8666, h8858, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p9078_1]
                      · have p9078_0 := h9078c.1
                        have p9078_1 := h9078c.2.1
                        have p9078_2 := h9078c.2.2.1
                        have p9078_3 := h9078c.2.2.2
                        linarith only [hlam, p9078_0]
            · linarith only [h6923, h8666, h8672, hlam]
          · linarith only [h5135, h8665, h8671, hlam]
        · linarith only [h5135, h8664, h8670, hlam]
      · linarith only [h0, h8663, h8669, hlam]
    · linarith only [h0, h8662, h8668, hlam]
  · linarith only [h0, h8661, h8667, hlam]

end R2N4
