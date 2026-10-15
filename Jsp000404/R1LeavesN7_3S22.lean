import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9670000 in
set_option maxHeartbeats 9670000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h8674 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8675 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8676 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8677 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8678 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 3 (by decide) (by decide) with h8679 | h8679
  · linarith only [h0, h4, h8674, h8679, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h8681 | h8681
    · rcases m.htr 1 2 5 (by decide) (by decide) with h8682 | h8682
      · rcases m.htr 1 3 4 (by decide) (by decide) with h8683 | h8683
        · rcases m.htr 1 3 5 (by decide) (by decide) with h8684 | h8684
          · rcases m.htr 1 4 5 (by decide) (by decide) with h8685 | h8685
            · rcases m.htr 2 3 4 (by decide) (by decide) with h8686 | h8686
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8687 | h8687
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8688 | h8688
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8689 | h8689
                    · rcases h1bigk with h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c | h8690c
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [hlam, p8690_0]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [h8681, h8686, h8689, hc01, hc45, hlam, hphi, ht0b, ht5b, p8690_1]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [h8679, h8681, h8686, h8689, hc01, hc45, hlam, hphi, ht0b, ht5b, p8690_1]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        rcases p8690_3 (m.d 0 1) (by simp) with h8694 | h8694
                        · rcases p8690_3 (m.d 1 2) (by simp) with h8695 | h8695
                          · linarith only [h0, h8695, hlam]
                          · linarith only [h8681, h8695, hlam]
                        · linarith only [h8694, hlam, p8690_0]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        rcases p8690_3 (m.d 0 1) (by simp) with h8699 | h8699
                        · rcases p8690_3 (m.d 1 2) (by simp) with h8700 | h8700
                          · linarith only [h0, h8700, hlam]
                          · linarith only [h8682, h8700, hlam]
                        · linarith only [h8699, hlam, p8690_0]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [h0, hlam, p8690_0]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [hlam, p8690_0]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [h8679, hlam, p8690_0]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [h0, h4, h8681, h8686, h8689, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8690_1]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        rcases p8690_3 (m.d 0 1) (by simp) with h8708 | h8708
                        · rcases p8690_3 (m.d 1 2) (by simp) with h8709 | h8709
                          · rcases p8690_3 (m.d 1 3) (by simp) with h8710 | h8710
                            · rcases p8690_3 (m.d 1 4) (by simp) with h8711 | h8711
                              · linarith only [h8681, h8711, hlam]
                              · linarith only [h8685, h8711, hlam]
                            · linarith only [h8684, h8710, hlam]
                          · linarith only [h8682, h8709, hlam]
                        · linarith only [h3, h8708, hlam]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [h1, hlam, p8690_0]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [h1, h8681, h8686, h8689, hc01, hc45, hlam, hphi, ht0b, ht5b, p8690_1]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [hlam, p8690_0]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [h1, h8681, h8686, h8689, hc01, hc45, hlam, hphi, ht0b, ht5b, p8690_1]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        rcases p8690_3 (m.d 0 1) (by simp) with h8721 | h8721
                        · rcases p8690_3 (m.d 1 2) (by simp) with h8722 | h8722
                          · linarith only [h8679, h8722, hlam]
                          · linarith only [h8682, h8722, hlam]
                        · linarith only [h3, h8721, hlam]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [h2, hlam, p8690_0]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [h8681, hlam, p8690_1]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [h8683, hlam, p8690_0]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [hlam, p8690_0]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        rcases p8690_3 (m.d 0 1) (by simp) with h8730 | h8730
                        · rcases p8690_3 (m.d 1 2) (by simp) with h8731 | h8731
                          · rcases p8690_3 (m.d 1 3) (by simp) with h8732 | h8732
                            · rcases p8690_3 (m.d 1 4) (by simp) with h8733 | h8733
                              · rcases p8690_3 (m.d 1 5) (by simp) with h8734 | h8734
                                · linarith only [h8685, h8734, hlam]
                                · rcases h3bigk with h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c | h8736c
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [hlam, p8736_0]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [h4, h8679, h8681, h8682, h8687, h8689, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8690_1, p8736_1]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [h4, hlam, p8736_1]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    rcases p8736_3 (m.d 0 3) (by simp) with h8740 | h8740
                                    · rcases p8736_3 (m.d 1 3) (by simp) with h8741 | h8741
                                      · linarith only [h1, h8741, hlam]
                                      · linarith only [h8683, h8741, hlam]
                                    · linarith only [h8740, hlam, p8736_0]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    rcases p8736_3 (m.d 0 3) (by simp) with h8745 | h8745
                                    · rcases p8736_3 (m.d 1 3) (by simp) with h8746 | h8746
                                      · linarith only [h1, h8746, hlam]
                                      · linarith only [h8684, h8746, hlam]
                                    · linarith only [h8745, hlam, p8736_0]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [h1, hlam, p8736_0]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [hlam, p8736_0]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [h8679, hlam, p8736_1]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [h1, h8689, hc01, hc45, hlam, hphi, ht0b, ht5b, p8736_1]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    rcases p8736_3 (m.d 0 3) (by simp) with h8754 | h8754
                                    · rcases p8736_3 (m.d 1 3) (by simp) with h8755 | h8755
                                      · rcases p8736_3 (m.d 2 3) (by simp) with h8756 | h8756
                                        · rcases p8736_3 (m.d 3 4) (by simp) with h8757 | h8757
                                          · linarith only [h8683, h8757, hlam]
                                          · linarith only [h8689, h8757, hlam]
                                        · linarith only [h8687, h8756, hlam]
                                      · linarith only [h8755, hlam, p8736_0]
                                    · linarith only [h8677, h8754, hlam]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [h0, h4, h8681, h8682, h8687, h8689, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8690_1, p8736_1]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [h8679, h8681, h8682, h8687, h8689, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8690_1, p8736_1]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [hlam, p8736_0]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    rcases p8736_3 (m.d 0 3) (by simp) with h8766 | h8766
                                    · linarith only [h4, h8766, hlam]
                                    · linarith only [h8676, h8766, hlam]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [h0, h4, h8681, h8682, h8687, hlam, p8690_1, p8736_2]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [h8676, hlam, p8736_0]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [h8683, hlam, p8736_0]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [h8686, hlam, p8736_0]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [hlam, p8736_0]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [h4, h8674, h8686, h8689, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8736_1]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [h8677, hlam, p8736_0]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [h8684, hlam, p8736_0]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [h8687, hlam, p8736_0]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [h8689, hlam, p8736_0]
                                  · have p8736_0 := h8736c.1
                                    have p8736_1 := h8736c.2.1
                                    have p8736_2 := h8736c.2.2.1
                                    have p8736_3 := h8736c.2.2.2
                                    linarith only [hlam, p8736_0]
                              · linarith only [h8685, h8733, hlam]
                            · linarith only [h8684, h8732, hlam]
                          · linarith only [h8682, h8731, hlam]
                        · linarith only [h3, h8730, hlam]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [h3, hlam, p8690_0]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [h8682, hlam, p8690_1]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [h8684, hlam, p8690_0]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [h8685, hlam, p8690_0]
                      · have p8690_0 := h8690c.1
                        have p8690_1 := h8690c.2.1
                        have p8690_2 := h8690c.2.2.1
                        have p8690_3 := h8690c.2.2.2
                        linarith only [hlam, p8690_0]
                    · linarith only [h0, h4, h8681, h8688, h8689, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8790 | h8790
                    · linarith only [h8686, h8688, h8790, hlam]
                    · rcases h1bigk with h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c | h8792c
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [hlam, p8792_0]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h8681, h8685, h8686, h8688, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8792_1]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h8679, h8681, h8685, h8686, h8688, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8792_1]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h8685, h8686, h8688, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8792_1]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        rcases p8792_3 (m.d 0 1) (by simp) with h8797 | h8797
                        · rcases p8792_3 (m.d 1 2) (by simp) with h8798 | h8798
                          · linarith only [h0, h8798, hlam]
                          · linarith only [h8682, h8798, hlam]
                        · linarith only [h8797, hlam, p8792_0]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h0, hlam, p8792_0]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [hlam, p8792_0]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h8679, hlam, p8792_0]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h8685, h8686, h8688, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8792_1]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h0, h4, h8685, h8686, h8688, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8792_1]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h1, hlam, p8792_0]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h1, h8681, h8686, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8792_1]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [hlam, p8792_0]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h1, h8685, h8686, h8688, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8792_1]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h1, h8685, h8686, h8688, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8792_1]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h2, hlam, p8792_0]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h8681, hlam, p8792_1]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h8683, hlam, p8792_0]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [hlam, p8792_0]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h0, h8681, h8685, h8686, h8688, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8792_1]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h3, hlam, p8792_0]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h8682, hlam, p8792_1]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h8684, hlam, p8792_0]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [h8685, hlam, p8792_0]
                      · have p8792_0 := h8792c.1
                        have p8792_1 := h8792c.2.1
                        have p8792_2 := h8792c.2.2.1
                        have p8792_3 := h8792c.2.2.2
                        linarith only [hlam, p8792_0]
                · linarith only [h4, h8677, h8687, hlam]
              · linarith only [h4, h8676, h8686, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h8824 | h8824
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8825 | h8825
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8826 | h8826
                  · linarith only [h8681, h8685, h8826, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8828 | h8828
                    · linarith only [h8681, h8685, h8824, h8828, hlam]
                    · rcases h1bigk with h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c | h8830c
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        linarith only [hlam, p8830_0]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        rcases p8830_3 (m.d 0 1) (by simp) with h8832 | h8832
                        · rcases p8830_3 (m.d 1 2) (by simp) with h8833 | h8833
                          · linarith only [h8833, hlam, p8830_0]
                          · rcases p8830_3 (m.d 1 3) (by simp) with h8835 | h8835
                            · linarith only [h1, h8835, hlam]
                            · linarith only [h8679, h8835, hlam]
                        · linarith only [h8832, hlam, p8830_0]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        rcases p8830_3 (m.d 0 1) (by simp) with h8839 | h8839
                        · rcases p8830_3 (m.d 1 2) (by simp) with h8840 | h8840
                          · linarith only [h0, h8840, hlam]
                          · rcases p8830_3 (m.d 1 3) (by simp) with h8842 | h8842
                            · linarith only [h8842, hlam, p8830_0]
                            · rcases p8830_3 (m.d 1 4) (by simp) with h8844 | h8844
                              · linarith only [h2, h8844, hlam]
                              · rcases p8830_3 (m.d 1 5) (by simp) with h8846 | h8846
                                · linarith only [h3, h8846, hlam]
                                · rcases h3bigk with h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c | h8848c
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [hlam, p8848_0]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    rcases p8848_3 (m.d 0 3) (by simp) with h8850 | h8850
                                    · rcases p8848_3 (m.d 1 3) (by simp) with h8851 | h8851
                                      · linarith only [h1, h8851, hlam]
                                      · rcases p8848_3 (m.d 2 3) (by simp) with h8853 | h8853
                                        · rcases p8848_3 (m.d 3 4) (by simp) with h8854 | h8854
                                          · linarith only [h8676, h8854, hlam]
                                          · rcases p8848_3 (m.d 3 5) (by simp) with h8856 | h8856
                                            · linarith only [h8677, h8856, hlam]
                                            · rcases h5bigk with h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c | h8858c
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [hlam, p8858_0]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h4, h8674, h8678, h8681, h8685, h8824, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8858_1]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h4, h8674, h8678, h8824, h8826, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8858_1]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h4, h8674, h8678, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p8858_1]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h4, h8674, h8678, h8681, h8685, h8824, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8858_1]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h3, hlam, p8858_0]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [hlam, p8858_0]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h3, h8824, h8826, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8858_1]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h8679, h8682, hc03, hc35, hlam, hphi, ht0b, ht5b, p8848_1, p8858_1]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h8685, hlam, p8858_1]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h8675, hlam, p8858_1]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h8682, hlam, p8858_1]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [hlam, p8858_0]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h4, h8675, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p8858_1]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h8826, hlam, p8858_1]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h8677, hlam, p8858_0]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h8684, hlam, p8858_0]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h8825, hlam, p8858_0]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [hlam, p8858_0]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h8828, hlam, p8858_1]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h8678, hlam, p8858_0]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h4, h8674, h8678, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p8858_1]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h4, h8674, h8678, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p8858_1]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [h4, h8674, h8678, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p8858_1]
                                              · have p8858_0 := h8858c.1
                                                have p8858_1 := h8858c.2.1
                                                have p8858_2 := h8858c.2.2.1
                                                have p8858_3 := h8858c.2.2.2
                                                linarith only [hlam, p8858_0]
                                        · linarith only [h8679, h8853, hlam]
                                    · linarith only [h1, h8850, hlam]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [h4, hlam, p8848_1]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    rcases p8848_3 (m.d 0 3) (by simp) with h8887 | h8887
                                    · rcases p8848_3 (m.d 1 3) (by simp) with h8888 | h8888
                                      · linarith only [h1, h8888, hlam]
                                      · linarith only [h8683, h8888, hlam]
                                    · linarith only [h8887, hlam, p8848_0]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    rcases p8848_3 (m.d 0 3) (by simp) with h8892 | h8892
                                    · rcases p8848_3 (m.d 1 3) (by simp) with h8893 | h8893
                                      · linarith only [h1, h8893, hlam]
                                      · linarith only [h8684, h8893, hlam]
                                    · linarith only [h8892, hlam, p8848_0]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [h1, hlam, p8848_0]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [hlam, p8848_0]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [h8679, hlam, p8848_1]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8830_1, p8848_1]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [h8828, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8830_1, p8848_1]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [h4, h8674, h8678, h8681, h8685, h8824, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8848_1]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    rcases p8848_3 (m.d 0 3) (by simp) with h8903 | h8903
                                    · linarith only [h4, h8903, hlam]
                                    · linarith only [h1, h8903, hlam]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [hlam, p8848_0]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [h4, h8674, h8678, h8681, h8685, h8824, hlam, p8848_2]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    rcases p8848_3 (m.d 0 3) (by simp) with h8908 | h8908
                                    · linarith only [h4, h8908, hlam]
                                    · linarith only [h8677, h8908, hlam]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [h8676, hlam, p8848_0]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [h8683, hlam, p8848_0]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [h8824, hlam, p8848_0]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [hlam, p8848_0]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [h8828, hlam, p8848_1]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [h8677, hlam, p8848_0]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [h8684, hlam, p8848_0]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [h8825, hlam, p8848_0]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [h0, h8682, h8825, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8848_1]
                                  · have p8848_0 := h8848c.1
                                    have p8848_1 := h8848c.2.1
                                    have p8848_2 := h8848c.2.2.1
                                    have p8848_3 := h8848c.2.2.2
                                    linarith only [hlam, p8848_0]
                        · linarith only [h8839, hlam, p8830_0]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        rcases p8830_3 (m.d 0 1) (by simp) with h8922 | h8922
                        · rcases p8830_3 (m.d 1 2) (by simp) with h8923 | h8923
                          · linarith only [h0, h8923, hlam]
                          · linarith only [h8681, h8923, hlam]
                        · linarith only [h8922, hlam, p8830_0]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        rcases p8830_3 (m.d 0 1) (by simp) with h8927 | h8927
                        · rcases p8830_3 (m.d 1 2) (by simp) with h8928 | h8928
                          · linarith only [h0, h8928, hlam]
                          · linarith only [h8682, h8928, hlam]
                        · linarith only [h8927, hlam, p8830_0]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        linarith only [h0, hlam, p8830_0]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        linarith only [hlam, p8830_0]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        linarith only [h8679, hlam, p8830_0]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        rcases p8830_3 (m.d 0 1) (by simp) with h8935 | h8935
                        · rcases p8830_3 (m.d 1 2) (by simp) with h8936 | h8936
                          · rcases p8830_3 (m.d 1 3) (by simp) with h8937 | h8937
                            · rcases p8830_3 (m.d 1 4) (by simp) with h8938 | h8938
                              · linarith only [h8681, h8938, hlam]
                              · rcases p8830_3 (m.d 1 5) (by simp) with h8940 | h8940
                                · linarith only [h8682, h8940, hlam]
                                · linarith only [h8685, h8940, hlam]
                            · linarith only [h8683, h8937, hlam]
                          · linarith only [h8681, h8936, hlam]
                        · linarith only [h2, h8935, hlam]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        rcases p8830_3 (m.d 0 1) (by simp) with h8946 | h8946
                        · rcases p8830_3 (m.d 1 2) (by simp) with h8947 | h8947
                          · rcases p8830_3 (m.d 1 3) (by simp) with h8948 | h8948
                            · rcases p8830_3 (m.d 1 4) (by simp) with h8949 | h8949
                              · linarith only [h8681, h8949, hlam]
                              · rcases p8830_3 (m.d 1 5) (by simp) with h8951 | h8951
                                · linarith only [h8682, h8951, hlam]
                                · rcases h3bigk with h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c | h8953c
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [hlam, p8953_0]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [h8679, h8685, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p8830_1, p8953_1]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [h4, hlam, p8953_1]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    rcases p8953_3 (m.d 0 3) (by simp) with h8957 | h8957
                                    · rcases p8953_3 (m.d 1 3) (by simp) with h8958 | h8958
                                      · linarith only [h1, h8958, hlam]
                                      · linarith only [h8683, h8958, hlam]
                                    · linarith only [h8957, hlam, p8953_0]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    rcases p8953_3 (m.d 0 3) (by simp) with h8962 | h8962
                                    · rcases p8953_3 (m.d 1 3) (by simp) with h8963 | h8963
                                      · linarith only [h1, h8963, hlam]
                                      · linarith only [h8684, h8963, hlam]
                                    · linarith only [h8962, hlam, p8953_0]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [h1, hlam, p8953_0]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [hlam, p8953_0]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [h8679, hlam, p8953_1]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    rcases p8953_3 (m.d 0 3) (by simp) with h8970 | h8970
                                    · rcases p8953_3 (m.d 1 3) (by simp) with h8971 | h8971
                                      · rcases p8953_3 (m.d 2 3) (by simp) with h8972 | h8972
                                        · rcases p8953_3 (m.d 3 4) (by simp) with h8973 | h8973
                                          · linarith only [h8973, hlam, p8953_0]
                                          · rcases p8953_3 (m.d 3 5) (by simp) with h8975 | h8975
                                            · linarith only [h8684, h8975, hlam]
                                            · linarith only [h8828, h8975, hlam]
                                        · linarith only [h8824, h8972, hlam]
                                      · linarith only [h8971, hlam, p8953_0]
                                    · linarith only [h8676, h8970, hlam]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    rcases p8953_3 (m.d 0 3) (by simp) with h8981 | h8981
                                    · rcases p8953_3 (m.d 1 3) (by simp) with h8982 | h8982
                                      · rcases p8953_3 (m.d 2 3) (by simp) with h8983 | h8983
                                        · rcases p8953_3 (m.d 3 4) (by simp) with h8984 | h8984
                                          · linarith only [h8683, h8984, hlam]
                                          · rcases p8953_3 (m.d 3 5) (by simp) with h8986 | h8986
                                            · linarith only [h8986, hlam, p8953_0]
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
                                                linarith only [h4, h8674, h8678, h8681, h8685, h8824, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h4, h8674, h8678, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h4, h8674, h8678, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h4, h8674, h8678, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h3, hlam, p8988_0]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [hlam, p8988_0]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h1, h8679, h8825, hc01, hc35, hlam, hphi, ht0b, ht5b, p8830_1, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h0, h4, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p8830_1, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8685, hlam, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8675, hlam, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8682, hlam, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [hlam, p8988_0]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h4, h8675, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8826, hlam, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8677, hlam, p8988_0]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8684, hlam, p8988_0]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8825, hlam, p8988_0]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [hlam, p8988_0]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8828, hlam, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h8678, hlam, p8988_0]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h4, h8674, h8678, h8682, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h4, h8674, h8678, h8825, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [h4, h8674, h8678, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p8988_1]
                                              · have p8988_0 := h8988c.1
                                                have p8988_1 := h8988c.2.1
                                                have p8988_2 := h8988c.2.2.1
                                                have p8988_3 := h8988c.2.2.2
                                                linarith only [hlam, p8988_0]
                                        · linarith only [h8825, h8983, hlam]
                                      · linarith only [h8982, hlam, p8953_0]
                                    · linarith only [h8677, h8981, hlam]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [h0, h4, h8681, h8685, h8824, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8830_1, p8953_1]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [h8679, h8681, h8685, h8824, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8830_1, p8953_1]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [hlam, p8953_0]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [h0, h4, h8681, h8685, h8824, hlam, p8830_1, p8953_2]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [h0, h4, h8684, hlam, p8830_1, p8953_2]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [h8676, hlam, p8953_0]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [h8683, hlam, p8953_0]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [h8824, hlam, p8953_0]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [hlam, p8953_0]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [h8828, hlam, p8953_1]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [h8677, hlam, p8953_0]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [h8684, hlam, p8953_0]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [h8825, hlam, p8953_0]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [h0, h8682, h8825, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p8830_1, p8953_1]
                                  · have p8953_0 := h8953c.1
                                    have p8953_1 := h8953c.2.1
                                    have p8953_2 := h8953c.2.2.1
                                    have p8953_3 := h8953c.2.2.2
                                    linarith only [hlam, p8953_0]
                            · linarith only [h8684, h8948, hlam]
                          · linarith only [h8682, h8947, hlam]
                        · linarith only [h3, h8946, hlam]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        linarith only [h1, hlam, p8830_0]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        linarith only [h1, h8681, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p8830_1]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        linarith only [hlam, p8830_0]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        rcases p8830_3 (m.d 0 1) (by simp) with h9038 | h9038
                        · rcases p8830_3 (m.d 1 2) (by simp) with h9039 | h9039
                          · linarith only [h8679, h9039, hlam]
                          · linarith only [h8681, h9039, hlam]
                        · linarith only [h2, h9038, hlam]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        rcases p8830_3 (m.d 0 1) (by simp) with h9043 | h9043
                        · rcases p8830_3 (m.d 1 2) (by simp) with h9044 | h9044
                          · linarith only [h8679, h9044, hlam]
                          · linarith only [h8682, h9044, hlam]
                        · linarith only [h3, h9043, hlam]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        linarith only [h2, hlam, p8830_0]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        linarith only [h8681, hlam, p8830_1]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        linarith only [h8683, hlam, p8830_0]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        linarith only [hlam, p8830_0]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        linarith only [h8685, hlam, p8830_1]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        linarith only [h3, hlam, p8830_0]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        linarith only [h8682, hlam, p8830_1]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        linarith only [h8684, hlam, p8830_0]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        linarith only [h4, h8674, h8678, h8681, h8685, h8824, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8830_1]
                      · have p8830_0 := h8830c.1
                        have p8830_1 := h8830c.2.1
                        have p8830_2 := h8830c.2.2.1
                        have p8830_3 := h8830c.2.2.2
                        linarith only [hlam, p8830_0]
                · linarith only [h4, h8674, h8678, h8684, h8685, h8825, hlam]
              · linarith only [h4, h8676, h8824, hlam]
          · linarith only [h8679, h8682, h8684, hlam]
        · linarith only [h8679, h8681, h8683, hlam]
      · linarith only [h4, h8675, h8681, h8682, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
    · linarith only [h4, h8674, h8681, hc12, hc23, hlam, hphi]

end R2N4
