import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_16S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_21_15_H_I_L_I_s10_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6137 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7252 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8021 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8693 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8694 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h6137 := hg6137
  have h7252 := hg7252
  have h8021 := hg8021
  rcases m.htr 0 2 5 (by decide) (by decide) with h9706 | h9706
  · rcases m.htr 0 3 4 (by decide) (by decide) with h9707 | h9707
    · linarith only [h8693, h8694, h9707, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h9709 | h9709
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9710 | h9710
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9711 | h9711
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9712 | h9712
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9713 | h9713
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9714 | h9714
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9715 | h9715
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9716 | h9716
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9717 | h9717
                      · linarith only [h8021, h8693, h8694, h9707, h9709, h9712, h9717, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9719 | h9719
                        · linarith only [h8693, h8694, h9711, h9714, h9717, h9719, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h8693, h8694, h9709, h9711, h9714, h9717, h9719, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h7252, h9710, h9716, hlam]
                  · linarith only [h9707, h9709, h9714, h9715, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9724 | h9724
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9725 | h9725
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9726 | h9726
                      · linarith only [h8693, h8694, h9712, h9714, h9726, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9728 | h9728
                        · linarith only [h8693, h8694, h9712, h9728, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h6137, h9709, h9714, h9728, hc23, hc34, hlam, hphi]
                    · linarith only [h8693, h8694, h9712, h9725, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h6137, h9709, h9724, hlam]
              · linarith only [h8693, h8694, h9712, h9713, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9734 | h9734
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9735 | h9735
                · linarith only [h9707, h9709, h9711, h9712, h9735, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9737 | h9737
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9738 | h9738
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9739 | h9739
                      · linarith only [h0, h7252, h8693, h9712, h9735, h9739, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9741 | h9741
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h9742 | h9742
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h9743 | h9743
                            · rcases h1bigk with h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c | h9744c
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [hlam, p9744_0]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [h0, hlam, p9744_0]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [h6137, hlam, p9744_0]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [h7252, hlam, p9744_0]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [h8021, hlam, p9744_0]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [hc01, hc12, hlam, hphi, p9744_1]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [hlam, p9744_0]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [h9712, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p9744_1]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [h9712, hlam, p9744_0]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [h8021, h9712, h9739, hc01, hc34, hlam, hphi, ht12, ht23, p9744_1]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [hc01, hc13, hlam, hphi, p9744_1]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [h9711, hlam, p9744_1]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [hlam, p9744_0]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [h9735, hlam, p9744_1]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [h8021, h9711, h9712, h9739, hc01, hc34, hlam, hphi, ht12, ht23, p9744_1]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [hc01, hc14, hlam, hphi, p9744_1]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [h0, h9712, h9739, hc02, hc34, hlam, hphi, ht23, p9744_1]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [h9712, h9739, hc13, hc34, hlam, hphi, p9744_1]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [hlam, p9744_0]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [h8021, h9712, h9739, hc01, hc34, hlam, hphi, ht12, ht23, p9744_1]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [h9737, hc01, hc13, hlam, hphi, p9744_1]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [h9734, hlam, p9744_1]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [h9737, hlam, p9744_0]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [h9738, hlam, p9744_0]
                              · have p9744_0 := h9744c.1
                                have p9744_1 := h9744c.2.1
                                have p9744_2 := h9744c.2.2.1
                                have p9744_3 := h9744c.2.2.2
                                linarith only [hlam, p9744_0]
                            · linarith only [h0, h9712, h9739, h9743, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h0, h8693, h9710, h9712, h9741, h9742, hc05, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h8693, h9709, h9712, h9739, h9741, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h7252, h8693, h9709, h9710, h9712, h9738, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h6137, h7252, h8693, h8694, h9709, h9737, hc01, hc14, hlam, hphi]
              · linarith only [h0, h9706, h9734, hlam]
          · linarith only [h0, h8693, h9711, hlam]
        · linarith only [h8693, h8694, h9709, h9710, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9778 | h9778
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9779 | h9779
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9780 | h9780
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9781 | h9781
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9782 | h9782
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9783 | h9783
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9784 | h9784
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9785 | h9785
                      · linarith only [h8693, h8694, h9707, h9780, h9785, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9787 | h9787
                        · linarith only [h6137, h8693, h8694, h9709, h9779, h9782, h9785, h9787, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h9789 | h9789
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h9790 | h9790
                            · rcases h1bigk with h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c | h9791c
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [hlam, p9791_0]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [h0, hlam, p9791_0]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [h6137, hlam, p9791_0]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [h7252, hlam, p9791_0]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [h8021, hlam, p9791_0]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [hc01, hc12, hlam, hphi, p9791_1]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [hlam, p9791_0]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [h8694, h9706, h9782, h9785, h9787, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9791_1]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [h8694, h9706, h9782, h9785, h9787, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9791_1]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [h6137, h9709, h9783, hc01, hc12, hlam, hphi, p9791_1]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [hc01, hc13, hlam, hphi, p9791_1]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [h9779, hlam, p9791_1]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [hlam, p9791_0]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [h8694, h9706, h9779, h9782, h9785, h9787, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9791_1]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [h6137, h9709, h9779, h9783, hc01, hc12, hlam, hphi, p9791_1]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [hc01, hc14, hlam, hphi, p9791_1]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [h9780, hlam, p9791_1]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [h9782, hlam, p9791_0]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [hlam, p9791_0]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [h6137, h9709, h9779, h9782, h9783, hc01, hc12, hlam, hphi, p9791_1]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [hc01, hc15, hlam, hphi, p9791_1]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [h9781, hlam, p9791_1]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [h9783, hlam, p9791_0]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [h9784, hlam, p9791_0]
                              · have p9791_0 := h9791c.1
                                have p9791_1 := h9791c.2.1
                                have p9791_2 := h9791c.2.2.1
                                have p9791_3 := h9791c.2.2.2
                                linarith only [hlam, p9791_0]
                            · linarith only [h8694, h9706, h9785, h9789, h9790, hlam]
                          · linarith only [h8694, h9706, h9787, h9789, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h7252, h9778, h9784, hlam]
                  · linarith only [h8693, h8694, h9707, h9782, h9783, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9821 | h9821
                  · linarith only [h6137, h9709, h9782, h9821, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9823 | h9823
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9824 | h9824
                      · linarith only [h8693, h8694, h9782, h9824, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9826 | h9826
                        · linarith only [h6137, h8693, h8694, h9780, h9821, h9826, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h9828 | h9828
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h9829 | h9829
                            · rcases h1bigk with h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c | h9830c
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [hlam, p9830_0]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [h0, hlam, p9830_0]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [h6137, hlam, p9830_0]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [h7252, hlam, p9830_0]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [h8021, hlam, p9830_0]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [hc01, hc12, hlam, hphi, p9830_1]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [hlam, p9830_0]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [h6137, hc01, hc12, hlam, hphi, p9830_1]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [h8694, h9780, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p9830_1]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [h8021, hc01, hc12, hlam, hphi, p9830_1]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [hc01, hc13, hlam, hphi, p9830_1]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [h9779, hlam, p9830_1]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [hlam, p9830_0]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [h9782, hlam, p9830_1]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [h9821, hlam, p9830_1]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [hc01, hc14, hlam, hphi, p9830_1]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [h9780, hlam, p9830_1]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [h9782, hc13, hc34, hlam, hphi, p9830_1]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [hlam, p9830_0]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [h6137, h9782, h9821, hc01, hc34, hlam, hphi, ht12, ht23, p9830_1]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [hc01, hc15, hlam, hphi, p9830_1]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [h9781, hlam, p9830_1]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [h6137, h9821, hc01, hc35, hlam, hphi, ht12, ht23, p9830_1]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [h9823, hlam, p9830_0]
                              · have p9830_0 := h9830c.1
                                have p9830_1 := h9830c.2.1
                                have p9830_2 := h9830c.2.2.1
                                have p9830_3 := h9830c.2.2.2
                                linarith only [hlam, p9830_0]
                            · linarith only [h7252, h8694, h9706, h9782, h9828, h9829, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h8693, h8694, h9828, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h8694, h9706, h9778, h9780, h9823, hc04, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h8693, h8694, h9780, h9781, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9860 | h9860
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9861 | h9861
                · linarith only [h6137, h9707, h9779, h9780, h9861, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9863 | h9863
                  · linarith only [h6137, h9709, h9861, h9863, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9865 | h9865
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9866 | h9866
                      · linarith only [h0, h7252, h8693, h9780, h9861, h9866, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9868 | h9868
                        · linarith only [h6137, h9863, h9868, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h9870 | h9870
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h9871 | h9871
                            · rcases h1bigk with h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c | h9872c
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h0, hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h6137, hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h7252, hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h8021, hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hc01, hc12, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h6137, h9780, hc01, hc14, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9780, hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h8021, h9780, hc01, hc14, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hc01, hc13, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9779, hlam, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9861, hlam, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9863, hlam, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hc01, hc14, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9780, h9866, hc13, hc34, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h8021, h9780, h9866, hc01, hc34, hlam, hphi, ht12, ht23, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hc01, hc15, hlam, hphi, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9860, hlam, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h6137, h9780, h9860, h9866, hc01, hc34, hlam, hphi, ht12, ht23, p9872_1]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [h9865, hlam, p9872_0]
                              · have p9872_0 := h9872c.1
                                have p9872_1 := h9872c.2.1
                                have p9872_2 := h9872c.2.2.1
                                have p9872_3 := h9872c.2.2.2
                                linarith only [hlam, p9872_0]
                            · linarith only [h0, h9706, h9780, h9866, h9870, h9871, hlam]
                          · linarith only [h0, h9706, h9780, h9868, h9870, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h7252, h9778, h9865, hlam]
              · linarith only [h0, h9706, h9860, hlam]
          · linarith only [h0, h8693, h9779, hlam]
        · linarith only [h8694, h9706, h9778, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h9904 | h9904
    · linarith only [h8693, h8694, h9904, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h9906 | h9906
      · linarith only [h8693, h9706, h9906, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9908 | h9908
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9909 | h9909
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9910 | h9910
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9911 | h9911
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9912 | h9912
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9913 | h9913
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9914 | h9914
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9915 | h9915
                      · linarith only [h8693, h8694, h9904, h9910, h9915, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9917 | h9917
                        · linarith only [h6137, h8693, h8694, h9906, h9909, h9912, h9915, h9917, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h9919 | h9919
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h9920 | h9920
                            · rcases h1bigk with h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c | h9921c
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [hlam, p9921_0]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [h0, hlam, p9921_0]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [h6137, hlam, p9921_0]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [h7252, hlam, p9921_0]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [h8021, hlam, p9921_0]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [hc01, hc12, hlam, hphi, p9921_1]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [hlam, p9921_0]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [h8693, h9706, h9912, h9915, h9919, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9921_1]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [h7252, hc01, hc12, hlam, hphi, p9921_1]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [h8693, h9706, h9913, h9917, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9921_1]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [hc01, hc13, hlam, hphi, p9921_1]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [h9909, hlam, p9921_1]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [hlam, p9921_0]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [h8693, h9706, h9909, h9910, h9919, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9921_1]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [h8693, h9706, h9909, h9913, h9917, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9921_1]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [hc01, hc14, hlam, hphi, p9921_1]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [h9910, hlam, p9921_1]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [h9912, hlam, p9921_0]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [hlam, p9921_0]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [h8693, h9706, h9909, h9912, h9913, h9917, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9921_1]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [hc01, hc15, hlam, hphi, p9921_1]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [h9911, hlam, p9921_1]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [h9913, hlam, p9921_0]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [h9914, hlam, p9921_0]
                              · have p9921_0 := h9921c.1
                                have p9921_1 := h9921c.2.1
                                have p9921_2 := h9921c.2.2.1
                                have p9921_3 := h9921c.2.2.2
                                linarith only [hlam, p9921_0]
                            · linarith only [h8693, h9706, h9908, h9915, h9919, h9920, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · linarith only [h8694, h9908, h9919, hlam]
                    · linarith only [h7252, h8694, h9908, h9914, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h8693, h8694, h9904, h9912, h9913, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9951 | h9951
                  · linarith only [h6137, h9906, h9912, h9951, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9953 | h9953
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9954 | h9954
                      · linarith only [h8693, h9706, h9912, h9954, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9956 | h9956
                        · linarith only [h8693, h9706, h9911, h9951, h9956, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h9958 | h9958
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h9959 | h9959
                            · rcases h1bigk with h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c | h9960c
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [hlam, p9960_0]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [h0, hlam, p9960_0]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [h6137, hlam, p9960_0]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [h7252, hlam, p9960_0]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [h8021, hlam, p9960_0]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [hc01, hc12, hlam, hphi, p9960_1]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [hlam, p9960_0]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [h6137, hc01, hc12, hlam, hphi, p9960_1]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [h9706, h9911, h9953, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p9960_1]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [h8693, h9706, h9911, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9960_1]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [hc01, hc13, hlam, hphi, p9960_1]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [h9909, hlam, p9960_1]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [hlam, p9960_0]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [h9912, hlam, p9960_1]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [h9951, hlam, p9960_1]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [hc01, hc14, hlam, hphi, p9960_1]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [h9910, hlam, p9960_1]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [h9912, hc13, hc34, hlam, hphi, p9960_1]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [hlam, p9960_0]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [h8693, h9706, h9911, h9912, hc23, hc34, hlam, hphi, p9960_1]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [hc01, hc15, hlam, hphi, p9960_1]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [h9911, hlam, p9960_1]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [h6137, h9951, hc01, hc35, hlam, hphi, ht12, ht23, p9960_1]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [h9953, hlam, p9960_0]
                              · have p9960_0 := h9960c.1
                                have p9960_1 := h9960c.2.1
                                have p9960_2 := h9960c.2.2.1
                                have p9960_3 := h9960c.2.2.2
                                linarith only [hlam, p9960_0]
                            · linarith only [h7252, h9908, h9912, h9959, hlam]
                          · linarith only [h8694, h9908, h9958, hlam]
                    · linarith only [h8694, h9908, h9910, h9953, hlam]
              · linarith only [h8693, h8694, h9910, h9911, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9990 | h9990
              · linarith only [h8693, h9706, h9910, h9990, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9992 | h9992
                · linarith only [h6137, h9904, h9909, h9910, h9992, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9994 | h9994
                  · linarith only [h6137, h9906, h9992, h9994, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9996 | h9996
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9997 | h9997
                      · linarith only [h0, h8693, h9910, h9992, h9997, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9999 | h9999
                        · linarith only [h6137, h8693, h9994, h9999, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10001 | h10001
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10002 | h10002
                            · rcases h1bigk with h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [hlam, p10003_0]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h0, hlam, p10003_0]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h6137, hlam, p10003_0]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h7252, hlam, p10003_0]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h8021, hlam, p10003_0]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h10001, h9990, h9997, hc01, hc34, hlam, hphi, ht12, ht23, p10003_1]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [hlam, p10003_0]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h10001, h6137, h9990, h9997, hc01, hc34, hlam, hphi, ht12, ht23, p10003_1]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h9910, hlam, p10003_0]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h9990, hlam, p10003_0]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [hc01, hc13, hlam, hphi, p10003_1]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h9909, hlam, p10003_1]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [hlam, p10003_0]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h9992, hlam, p10003_1]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h9994, hlam, p10003_1]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h9910, h9997, hc01, hc34, hlam, hphi, ht12, ht23, p10003_1]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h0, h9910, h9997, hc02, hc34, hlam, hphi, ht23, p10003_1]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h6137, h9910, h9997, hc01, hc34, hlam, hphi, ht12, ht23, p10003_1]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [hlam, p10003_0]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h8021, h9910, h9997, hc01, hc34, hlam, hphi, ht12, ht23, p10003_1]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [hc01, hc15, hlam, hphi, p10003_1]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h10001, h6137, h9909, h9990, h9997, hc01, hc34, hlam, hphi, ht12, ht23, p10003_1]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h10001, h6137, h9990, h9997, hc01, hc34, hlam, hphi, ht12, ht23, p10003_1]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [h9996, hlam, p10003_0]
                              · have p10003_0 := h10003c.1
                                have p10003_1 := h10003c.2.1
                                have p10003_2 := h10003c.2.2.1
                                have p10003_3 := h10003c.2.2.2
                                linarith only [hlam, p10003_0]
                            · linarith only [h10002, h7252, h9908, h9910, h9997, hlam]
                          · linarith only [h10001, h7252, h9908, h9910, hlam]
                    · linarith only [h7252, h9908, h9996, hlam]
          · linarith only [h0, h8693, h9909, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10033 | h10033
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10034 | h10034
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10035 | h10035
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10036 | h10036
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10037 | h10037
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10038 | h10038
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10039 | h10039
                      · linarith only [h10033, h10036, h10038, h10039, h6137, h8693, h8694, h9904, h9908, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10041 | h10041
                        · linarith only [h10033, h10036, h10038, h10041, h8693, h8694, h9908, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10043 | h10043
                          · linarith only [h10039, h10043, h8693, h8694, h9908, hc23, hc34, hlam, hphi]
                          · linarith only [h10033, h10036, h10038, h10043, h8693, h8694, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h10034, h10038, h8693, h8694, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h10036, h10037, h6137, h9904, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10048 | h10048
                  · linarith only [h10036, h10048, h6137, h9906, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10050 | h10050
                    · linarith only [h10036, h10050, h8693, h8694, h9908, hc23, hc34, hlam, hphi]
                    · linarith only [h10034, h10050, h8693, h8694, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h10034, h10035, h8693, h8694, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10054 | h10054
              · linarith only [h10034, h10054, h8693, h9706, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10056 | h10056
                · linarith only [h10033, h10034, h10056, h6137, h9904, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10058 | h10058
                  · linarith only [h10056, h10058, h6137, h9906, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10060 | h10060
                    · linarith only [h10056, h10060, h8693, h8694, h9908, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10062 | h10062
                      · linarith only [h0, h10034, h10060, h10062, h8693, hc34, hc45, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10064 | h10064
                        · linarith only [h0, h10034, h10058, h10060, h10064, h6137, h8693, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10066 | h10066
                          · linarith only [h0, h10034, h10060, h10062, h10066, h8693, hc23, hc34, hlam, hphi]
                          · linarith only [h10066, h8693, h8694, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h10033, h8693, h8694, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_21_15_H_I_L_I_s10_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6137 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7252 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8021 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8693 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h6137 := hg6137
  have h7252 := hg7252
  have h8021 := hg8021
  rcases m.htr 0 2 4 (by decide) (by decide) with h8694 | h8694
  · exact r1l7_21_15_H_I_L_I_s10_x0_x0 m hb1 hb5 hg0 hg6137 hg7252 hg8021 h8693 h8694
  · exact r1l7_21_15_H_I_L_I_s10_x0_x1 m hb1 hb5 hg0 hg6137 hg7252 hg8021 h8693 h8694

end R2N4
