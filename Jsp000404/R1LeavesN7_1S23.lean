import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S12
import Jsp000404.R1LeavesN7_1S21
import Jsp000404.R1LeavesN7_1S22

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12466000 in
set_option maxHeartbeats 12466000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h7821 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h7822 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 4 (by decide) (by decide) with h8656 | h8656
  · rcases m.htr 0 3 5 (by decide) (by decide) with h8657 | h8657
    · rcases m.htr 0 4 5 (by decide) (by decide) with h8658 | h8658
      · linarith only [h7821, h7822, h8658, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h8660 | h8660
        · linarith only [h0, h4, h8660, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h8662 | h8662
          · rcases m.htr 1 2 5 (by decide) (by decide) with h8663 | h8663
            · linarith only [h0, h7822, h8663, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h8665 | h8665
              · rcases m.htr 1 3 5 (by decide) (by decide) with h8666 | h8666
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8667 | h8667
                  · linarith only [h2, h8658, h8667, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h8669 | h8669
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h8670 | h8670
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h8671 | h8671
                        · linarith only [h0, h2, h7822, h8658, h8662, h8670, h8671, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h8673 | h8673
                          · linarith only [h7821, h7822, h8669, h8671, h8673, hlam]
                          · rcases h0bigk with h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c | h8675c
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              linarith only [hlam, p8675_0]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              rcases p8675_3 (m.d 0 1) (by simp) with h8677 | h8677
                              · rcases p8675_3 (m.d 0 2) (by simp) with h8678 | h8678
                                · linarith only [h0, h8678, hlam]
                                · rcases p8675_3 (m.d 0 3) (by simp) with h8680 | h8680
                                  · linarith only [h1, h8680, hlam]
                                  · linarith only [h4, h8680, hlam]
                              · linarith only [h0, h8677, hlam]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              rcases p8675_3 (m.d 0 1) (by simp) with h8684 | h8684
                              · rcases p8675_3 (m.d 0 2) (by simp) with h8685 | h8685
                                · linarith only [h0, h8685, hlam]
                                · rcases p8675_3 (m.d 0 3) (by simp) with h8687 | h8687
                                  · linarith only [h1, h8687, hlam]
                                  · rcases p8675_3 (m.d 0 4) (by simp) with h8689 | h8689
                                    · linarith only [h2, h8689, hlam]
                                    · rcases p8675_3 (m.d 0 5) (by simp) with h8691 | h8691
                                      · linarith only [h3, h8691, hlam]
                                      · rcases h2bigk with h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c | h8693c
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [hlam, p8693_0]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [h7822, h8662, h8669, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8693_1]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [h4, hlam, p8693_0]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [h4, h8669, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8675_1, p8693_1]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [h7822, hlam, p8693_0]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [h0, hlam, p8693_0]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [hlam, p8693_0]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [h8660, hlam, p8693_0]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [h0, h4, h8669, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8675_1, p8693_1]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [h8663, hlam, p8693_0]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          rcases p8693_3 (m.d 0 2) (by simp) with h8704 | h8704
                                          · linarith only [h8704, hlam, p8693_0]
                                          · rcases p8693_3 (m.d 1 2) (by simp) with h8706 | h8706
                                            · linarith only [h8660, h8706, hlam]
                                            · rcases p8693_3 (m.d 2 3) (by simp) with h8708 | h8708
                                              · rcases p8693_3 (m.d 2 4) (by simp) with h8709 | h8709
                                                · linarith only [h8669, h8709, hlam]
                                                · rcases p8693_3 (m.d 2 5) (by simp) with h8711 | h8711
                                                  · linarith only [h8670, h8711, hlam]
                                                  · linarith only [h7822, h8711, hlam]
                                              · linarith only [h8708, hlam, p8693_0]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          rcases p8693_3 (m.d 0 2) (by simp) with h8715 | h8715
                                          · linarith only [h4, h8715, hlam]
                                          · linarith only [h0, h8715, hlam]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [hlam, p8693_0]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          rcases p8693_3 (m.d 0 2) (by simp) with h8719 | h8719
                                          · linarith only [h4, h8719, hlam]
                                          · linarith only [h7821, h8719, hlam]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [h7822, hc02, hc23, hlam, hphi, p8693_1]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [h7821, hlam, p8693_0]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [h8662, hlam, p8693_0]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [h8669, hlam, p8693_1]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [hlam, p8693_0]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [h8671, hlam, p8693_1]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [h0, h8662, h8669, h8671, hc34, hc45, hlam, hphi, p8693_1]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [h8662, h8669, h8671, hc34, hc45, hlam, hphi, p8693_1]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [h8670, hlam, p8693_1]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          rcases p8693_3 (m.d 0 2) (by simp) with h8731 | h8731
                                          · linarith only [h7822, h8731, hlam]
                                          · linarith only [h7821, h8731, hlam]
                                        · have p8693_0 := h8693c.1
                                          have p8693_1 := h8693c.2.1
                                          have p8693_2 := h8693c.2.2.1
                                          have p8693_3 := h8693c.2.2.2
                                          linarith only [hlam, p8693_0]
                              · linarith only [h1, h8684, hlam]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              rcases p8675_3 (m.d 0 1) (by simp) with h8736 | h8736
                              · rcases p8675_3 (m.d 0 2) (by simp) with h8737 | h8737
                                · linarith only [h0, h8737, hlam]
                                · linarith only [h7821, h8737, hlam]
                              · linarith only [h2, h8736, hlam]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              rcases p8675_3 (m.d 0 1) (by simp) with h8741 | h8741
                              · rcases p8675_3 (m.d 0 2) (by simp) with h8742 | h8742
                                · linarith only [h0, h8742, hlam]
                                · rcases p8675_3 (m.d 0 3) (by simp) with h8744 | h8744
                                  · linarith only [h1, h8744, hlam]
                                  · linarith only [h8657, h8744, hlam]
                              · linarith only [h3, h8741, hlam]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              linarith only [h0, hlam, p8675_0]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              linarith only [hlam, p8675_0]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              linarith only [h4, hlam, p8675_0]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              linarith only [h7821, h7822, h8669, h8671, hc34, hc45, hlam, hphi, p8675_1]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              linarith only [h7822, hlam, p8675_0]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              linarith only [h1, hlam, p8675_1]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              rcases p8675_3 (m.d 0 1) (by simp) with h8754 | h8754
                              · rcases p8675_3 (m.d 0 2) (by simp) with h8755 | h8755
                                · linarith only [h4, h8755, hlam]
                                · rcases p8675_3 (m.d 0 3) (by simp) with h8757 | h8757
                                  · rcases p8675_3 (m.d 0 4) (by simp) with h8758 | h8758
                                    · linarith only [h8656, h8758, hlam]
                                    · rcases p8675_3 (m.d 0 5) (by simp) with h8760 | h8760
                                      · linarith only [h8657, h8760, hlam]
                                      · linarith only [h7822, h8760, hlam]
                                  · linarith only [h4, h8757, hlam]
                              · linarith only [h0, h8754, hlam]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              linarith only [hlam, p8675_0]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              rcases p8675_3 (m.d 0 1) (by simp) with h8766 | h8766
                              · rcases p8675_3 (m.d 0 2) (by simp) with h8767 | h8767
                                · linarith only [h4, h8767, hlam]
                                · linarith only [h7821, h8767, hlam]
                              · linarith only [h2, h8766, hlam]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              rcases p8675_3 (m.d 0 1) (by simp) with h8771 | h8771
                              · rcases p8675_3 (m.d 0 2) (by simp) with h8772 | h8772
                                · linarith only [h4, h8772, hlam]
                                · rcases p8675_3 (m.d 0 3) (by simp) with h8774 | h8774
                                  · rcases p8675_3 (m.d 0 4) (by simp) with h8775 | h8775
                                    · linarith only [h8656, h8775, hlam]
                                    · rcases p8675_3 (m.d 0 5) (by simp) with h8777 | h8777
                                      · linarith only [h8657, h8777, hlam]
                                      · rcases h2bigk with h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c | h8779c
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [hlam, p8779_0]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [h4, h7822, h8662, h8669, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8675_1, p8779_1]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [h4, hlam, p8779_0]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [h4, h7822, h8669, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8675_1, p8779_1]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [h7822, hlam, p8779_0]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [h0, hlam, p8779_0]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [hlam, p8779_0]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [h8660, hlam, p8779_0]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [h0, h4, h7822, h8669, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8675_1, p8779_1]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [h8663, hlam, p8779_0]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          rcases p8779_3 (m.d 0 2) (by simp) with h8790 | h8790
                                          · linarith only [h8790, hlam, p8779_0]
                                          · rcases p8779_3 (m.d 1 2) (by simp) with h8792 | h8792
                                            · linarith only [h8660, h8792, hlam]
                                            · rcases p8779_3 (m.d 2 3) (by simp) with h8794 | h8794
                                              · rcases p8779_3 (m.d 2 4) (by simp) with h8795 | h8795
                                                · linarith only [h8669, h8795, hlam]
                                                · rcases p8779_3 (m.d 2 5) (by simp) with h8797 | h8797
                                                  · linarith only [h8670, h8797, hlam]
                                                  · linarith only [h7822, h8797, hlam]
                                              · linarith only [h8794, hlam, p8779_0]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          rcases p8779_3 (m.d 0 2) (by simp) with h8801 | h8801
                                          · linarith only [h4, h8801, hlam]
                                          · linarith only [h0, h8801, hlam]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [hlam, p8779_0]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [h4, h7821, h7822, hlam, p8675_1, p8779_2]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [h7822, hc02, hc23, hlam, hphi, p8779_1]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [h7821, hlam, p8779_0]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [h8662, hlam, p8779_0]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [h8669, hlam, p8779_1]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [hlam, p8779_0]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [h8671, hlam, p8779_1]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [h0, h8662, h8669, h8671, hc34, hc45, hlam, hphi, p8779_1]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [h8662, h8669, h8671, hc34, hc45, hlam, hphi, p8779_1]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [h8670, hlam, p8779_1]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          rcases p8779_3 (m.d 0 2) (by simp) with h8815 | h8815
                                          · linarith only [h7822, h8815, hlam]
                                          · linarith only [h7821, h8815, hlam]
                                        · have p8779_0 := h8779c.1
                                          have p8779_1 := h8779c.2.1
                                          have p8779_2 := h8779c.2.2.1
                                          have p8779_3 := h8779c.2.2.2
                                          linarith only [hlam, p8779_0]
                                  · linarith only [h8657, h8774, hlam]
                              · linarith only [h3, h8771, hlam]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              linarith only [h2, hlam, p8675_0]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              linarith only [h7821, hlam, p8675_0]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              linarith only [h8656, hlam, p8675_0]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              linarith only [hlam, p8675_0]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              linarith only [h8658, hlam, p8675_0]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              linarith only [h3, hlam, p8675_0]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              linarith only [h0, h7822, h8662, h8669, h8671, hc34, hc45, hlam, hphi, p8675_1]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              linarith only [h8657, hlam, p8675_0]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              rcases p8675_3 (m.d 0 1) (by simp) with h8829 | h8829
                              · rcases p8675_3 (m.d 0 2) (by simp) with h8830 | h8830
                                · linarith only [h7822, h8830, hlam]
                                · linarith only [h7821, h8830, hlam]
                              · linarith only [h2, h8829, hlam]
                            · have p8675_0 := h8675c.1
                              have p8675_1 := h8675c.2.1
                              have p8675_2 := h8675c.2.2.1
                              have p8675_3 := h8675c.2.2.2
                              linarith only [hlam, p8675_0]
                      · linarith only [h4, h8657, h8670, hlam]
                    · linarith only [h4, h8656, h8669, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8837 | h8837
                  · linarith only [h2, h7821, h7822, h8658, h8837, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h8839 | h8839
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h8840 | h8840
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h8841 | h8841
                        · linarith only [h8657, h8658, h8660, h8662, h8666, h8841, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h8843 | h8843
                          · linarith only [h7821, h7822, h8839, h8841, h8843, hlam]
                          · rcases h0bigk with h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c | h8845c
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [hlam, p8845_0]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              rcases p8845_3 (m.d 0 1) (by simp) with h8847 | h8847
                              · rcases p8845_3 (m.d 0 2) (by simp) with h8848 | h8848
                                · linarith only [h0, h8848, hlam]
                                · rcases p8845_3 (m.d 0 3) (by simp) with h8850 | h8850
                                  · linarith only [h1, h8850, hlam]
                                  · linarith only [h4, h8850, hlam]
                              · linarith only [h0, h8847, hlam]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [h8657, h8666, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p8845_1]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              rcases p8845_3 (m.d 0 1) (by simp) with h8855 | h8855
                              · rcases p8845_3 (m.d 0 2) (by simp) with h8856 | h8856
                                · linarith only [h0, h8856, hlam]
                                · linarith only [h7821, h8856, hlam]
                              · linarith only [h2, h8855, hlam]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [h8657, h8660, h8662, h8666, h8839, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8845_1]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [h0, hlam, p8845_0]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [hlam, p8845_0]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [h4, hlam, p8845_0]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [h7821, h7822, h8839, h8841, hc34, hc45, hlam, hphi, p8845_1]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [h7822, hlam, p8845_0]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [h1, hlam, p8845_1]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              rcases p8845_3 (m.d 0 1) (by simp) with h8867 | h8867
                              · rcases p8845_3 (m.d 0 2) (by simp) with h8868 | h8868
                                · linarith only [h4, h8868, hlam]
                                · rcases p8845_3 (m.d 0 3) (by simp) with h8870 | h8870
                                  · rcases p8845_3 (m.d 0 4) (by simp) with h8871 | h8871
                                    · linarith only [h8656, h8871, hlam]
                                    · rcases p8845_3 (m.d 0 5) (by simp) with h8873 | h8873
                                      · linarith only [h8657, h8873, hlam]
                                      · linarith only [h7822, h8873, hlam]
                                  · linarith only [h4, h8870, hlam]
                              · linarith only [h0, h8867, hlam]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [hlam, p8845_0]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              rcases p8845_3 (m.d 0 1) (by simp) with h8879 | h8879
                              · rcases p8845_3 (m.d 0 2) (by simp) with h8880 | h8880
                                · linarith only [h4, h8880, hlam]
                                · linarith only [h7821, h8880, hlam]
                              · linarith only [h2, h8879, hlam]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [h4, h8657, h8660, h8662, h8666, h8839, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8845_1]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [h2, hlam, p8845_0]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [h7821, hlam, p8845_0]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [h8656, hlam, p8845_0]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [hlam, p8845_0]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [h8658, hlam, p8845_0]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [h3, hlam, p8845_0]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [h0, h7822, h8662, h8839, h8841, hc34, hc45, hlam, hphi, p8845_1]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [h8657, hlam, p8845_0]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              rcases p8845_3 (m.d 0 1) (by simp) with h8893 | h8893
                              · rcases p8845_3 (m.d 0 2) (by simp) with h8894 | h8894
                                · linarith only [h7822, h8894, hlam]
                                · linarith only [h7821, h8894, hlam]
                              · linarith only [h2, h8893, hlam]
                            · have p8845_0 := h8845c.1
                              have p8845_1 := h8845c.2.1
                              have p8845_2 := h8845c.2.2.1
                              have p8845_3 := h8845c.2.2.2
                              linarith only [hlam, p8845_0]
                      · linarith only [h4, h8657, h8840, hlam]
                    · linarith only [h4, h8657, h8660, h8662, h8666, h8839, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · linarith only [h8656, h8658, h8660, h8662, h8665, hc24, hc45, hlam, hphi]
          · linarith only [h7821, h7822, h8662, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h8903 | h8903
      · linarith only [h7821, h7822, h8903, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h8905 | h8905
        · linarith only [h0, h4, h7821, h8905, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h8907 | h8907
          · rcases m.htr 1 2 5 (by decide) (by decide) with h8908 | h8908
            · linarith only [h0, h7822, h8908, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h8910 | h8910
              · rcases m.htr 1 3 5 (by decide) (by decide) with h8911 | h8911
                · linarith only [h0, h1, h4, h8657, h8907, h8911, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8913 | h8913
                  · linarith only [h2, h8903, h8913, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h8915 | h8915
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h8916 | h8916
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h8917 | h8917
                        · linarith only [h0, h2, h4, h8657, h8903, h8907, h8916, h8917, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h8919 | h8919
                          · linarith only [h4, h7821, h8657, h8915, h8916, h8917, h8919, hlam]
                          · rcases h0bigk with h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c | h8921c
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [hlam, p8921_0]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              rcases p8921_3 (m.d 0 1) (by simp) with h8923 | h8923
                              · rcases p8921_3 (m.d 0 2) (by simp) with h8924 | h8924
                                · linarith only [h0, h8924, hlam]
                                · rcases p8921_3 (m.d 0 3) (by simp) with h8926 | h8926
                                  · linarith only [h1, h8926, hlam]
                                  · linarith only [h4, h8926, hlam]
                              · linarith only [h0, h8923, hlam]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              rcases p8921_3 (m.d 0 1) (by simp) with h8930 | h8930
                              · rcases p8921_3 (m.d 0 2) (by simp) with h8931 | h8931
                                · linarith only [h0, h8931, hlam]
                                · rcases p8921_3 (m.d 0 3) (by simp) with h8933 | h8933
                                  · linarith only [h1, h8933, hlam]
                                  · rcases p8921_3 (m.d 0 4) (by simp) with h8935 | h8935
                                    · linarith only [h2, h8935, hlam]
                                    · rcases p8921_3 (m.d 0 5) (by simp) with h8937 | h8937
                                      · linarith only [h3, h8937, hlam]
                                      · linarith only [h8657, h8937, hlam]
                              · linarith only [h1, h8930, hlam]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              rcases p8921_3 (m.d 0 1) (by simp) with h8941 | h8941
                              · rcases p8921_3 (m.d 0 2) (by simp) with h8942 | h8942
                                · linarith only [h0, h8942, hlam]
                                · linarith only [h7821, h8942, hlam]
                              · linarith only [h2, h8941, hlam]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              rcases p8921_3 (m.d 0 1) (by simp) with h8946 | h8946
                              · rcases p8921_3 (m.d 0 2) (by simp) with h8947 | h8947
                                · linarith only [h0, h8947, hlam]
                                · rcases p8921_3 (m.d 0 3) (by simp) with h8949 | h8949
                                  · linarith only [h1, h8949, hlam]
                                  · rcases p8921_3 (m.d 0 4) (by simp) with h8951 | h8951
                                    · linarith only [h2, h8951, hlam]
                                    · rcases p8921_3 (m.d 0 5) (by simp) with h8953 | h8953
                                      · linarith only [h3, h8953, hlam]
                                      · rcases h2bigk with h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [hlam, p8955_0]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [h4, h8657, h8907, h8915, h8916, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8955_1]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [h4, hlam, p8955_0]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [h4, h8657, h8915, h8916, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8955_1]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [h7822, hlam, p8955_0]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [h0, hlam, p8955_0]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [hlam, p8955_0]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [h8905, hlam, p8955_0]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [h0, h4, h8657, h8915, h8916, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8955_1]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [h8908, hlam, p8955_0]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          rcases p8955_3 (m.d 0 2) (by simp) with h8966 | h8966
                                          · linarith only [h8966, hlam, p8955_0]
                                          · rcases p8955_3 (m.d 1 2) (by simp) with h8968 | h8968
                                            · linarith only [h8905, h8968, hlam]
                                            · rcases p8955_3 (m.d 2 3) (by simp) with h8970 | h8970
                                              · rcases p8955_3 (m.d 2 4) (by simp) with h8971 | h8971
                                                · linarith only [h8915, h8971, hlam]
                                                · rcases p8955_3 (m.d 2 5) (by simp) with h8973 | h8973
                                                  · linarith only [h8916, h8973, hlam]
                                                  · linarith only [h7822, h8973, hlam]
                                              · linarith only [h8970, hlam, p8955_0]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          rcases p8955_3 (m.d 0 2) (by simp) with h8977 | h8977
                                          · linarith only [h4, h8977, hlam]
                                          · linarith only [h0, h8977, hlam]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [hlam, p8955_0]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [h4, h7821, h8657, h8916, hlam, p8955_2]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [h4, h8657, h8916, hc02, hc23, hlam, hphi, p8955_1]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [h7821, hlam, p8955_0]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [h8907, hlam, p8955_0]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [h8915, hlam, p8955_1]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [hlam, p8955_0]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [h8917, hlam, p8955_1]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [h0, h8907, h8917, hc24, hc45, hlam, hphi, p8955_1]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [h8907, h8917, hc24, hc45, hlam, hphi, p8955_1]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [h8916, hlam, p8955_1]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          rcases p8955_3 (m.d 0 2) (by simp) with h8991 | h8991
                                          · linarith only [h7822, h8991, hlam]
                                          · linarith only [h7821, h8991, hlam]
                                        · have p8955_0 := h8955c.1
                                          have p8955_1 := h8955c.2.1
                                          have p8955_2 := h8955c.2.2.1
                                          have p8955_3 := h8955c.2.2.2
                                          linarith only [hlam, p8955_0]
                              · linarith only [h3, h8946, hlam]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [h0, hlam, p8921_0]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [hlam, p8921_0]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [h4, hlam, p8921_0]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [h7821, h7822, h8915, h8917, hc34, hc45, hlam, hphi, p8921_1]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [h7822, hlam, p8921_0]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [h1, hlam, p8921_1]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [h8657, hc02, hc35, hlam, hphi, ht23, p8921_1]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [hlam, p8921_0]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [h2, h8657, h8907, h8915, h8916, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8921_1]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [h8657, hlam, p8921_1]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [h2, hlam, p8921_0]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [h7821, hlam, p8921_0]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [h8656, hlam, p8921_0]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [hlam, p8921_0]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [h8903, hlam, p8921_0]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [h3, hlam, p8921_0]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [h0, h7822, h8907, h8915, h8917, hc34, hc45, hlam, hphi, p8921_1]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [h0, h4, h8657, h8907, h8915, h8916, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8921_1]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              rcases p8921_3 (m.d 0 1) (by simp) with h9014 | h9014
                              · rcases p8921_3 (m.d 0 2) (by simp) with h9015 | h9015
                                · linarith only [h7822, h9015, hlam]
                                · linarith only [h7821, h9015, hlam]
                              · linarith only [h2, h9014, hlam]
                            · have p8921_0 := h8921c.1
                              have p8921_1 := h8921c.2.1
                              have p8921_2 := h8921c.2.2.1
                              have p8921_3 := h8921c.2.2.2
                              linarith only [hlam, p8921_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9020 | h9020
                        · linarith only [h0, h4, h8903, h8907, h8916, h9020, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9022 | h9022
                          · linarith only [h0, h4, h8907, h8915, h8916, h9020, h9022, hlam]
                          · linarith only [h0, h4, h8907, h8916, h9022, hc24, hc45, hlam, hphi]
                    · linarith only [h0, h4, h8656, h8907, h8915, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h8656, h8657, h8905, h8907, h8910, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · linarith only [h4, h7821, h8907, hc12, hc23, hlam, hphi]
  · linarith only [h4, h7821, h8656, hlam]

set_option maxHeartbeats 12466000 in
set_option maxHeartbeats 12466000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h7821 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 5 (by decide) (by decide) with h7822 | h7822
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h7821 h7822
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h7821 h7822

set_option maxHeartbeats 12466000 in
set_option maxHeartbeats 12466000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s12 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h7821

set_option maxHeartbeats 12466000 in
set_option maxHeartbeats 12466000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h7821 | h7821
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h7821
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h7821

set_option maxHeartbeats 28100000 in
set_option maxHeartbeats 28100000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s3 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s4 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 28348000 in
set_option maxHeartbeats 28348000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s2 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s3 m hb0 hb2 hb3 hb5 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h14054 | h14054
    · rcases m.htr 0 2 4 (by decide) (by decide) with h14055 | h14055
      · rcases m.htr 0 2 5 (by decide) (by decide) with h14056 | h14056
        · linarith only [h0, h14056, h3, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h14058 | h14058
          · rcases m.htr 0 3 5 (by decide) (by decide) with h14059 | h14059
            · linarith only [h1, h14059, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14061 | h14061
              · linarith only [h14061, h2, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14063 | h14063
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14064 | h14064
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14065 | h14065
                    · linarith only [h0, h14056, h14065, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14067 | h14067
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14068 | h14068
                        · linarith only [h0, h14058, h14059, h14063, h14065, h14068, h2, h3, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h14063, h14068, h3, hc23, hc35, hlam, hphi]
                      · linarith only [h14058, h14059, h14067, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h14055, h14063, h14064, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h14054, h14056, h14063, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h14074 | h14074
            · linarith only [h1, h14074, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14076 | h14076
              · linarith only [h0, h14055, h14076, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14078 | h14078
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14079 | h14079
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14080 | h14080
                    · linarith only [h0, h14056, h14080, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14082 | h14082
                      · linarith only [h1, h14058, h14082, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14084 | h14084
                        · linarith only [h1, h14074, h14084, hlam]
                        · linarith only [h0, h14078, h14084, h3, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h14055, h14078, h14079, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h14054, h14056, h14078, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h14089 | h14089
        · linarith only [h0, h14089, h3, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h14091 | h14091
          · linarith only [h14054, h14055, h14091, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h14093 | h14093
            · linarith only [h14054, h14055, h14093, h2, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14095 | h14095
              · linarith only [h14095, h2, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14097 | h14097
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14098 | h14098
                  · linarith only [h0, h14055, h14098, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14100 | h14100
                    · linarith only [h0, h14089, h14100, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14102 | h14102
                      · linarith only [h1, h14091, h14102, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14104 | h14104
                        · linarith only [h1, h14093, h14104, hlam]
                        · linarith only [h0, h14097, h14104, h3, hc23, hc35, hlam, hphi]
                · linarith only [h14054, h14055, h14097, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h14108 | h14108
      · rcases m.htr 0 2 5 (by decide) (by decide) with h14109 | h14109
        · linarith only [h0, h14109, h3, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h14111 | h14111
          · rcases m.htr 0 3 5 (by decide) (by decide) with h14112 | h14112
            · linarith only [h1, h14112, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14114 | h14114
              · linarith only [h1, h14054, h14108, h14114, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14116 | h14116
                · linarith only [h0, h14054, h14116, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14118 | h14118
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14119 | h14119
                    · linarith only [h0, h14109, h14119, h3, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14121 | h14121
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14122 | h14122
                        · linarith only [h0, h1, h14054, h14112, h14118, h14122, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h14124 | h14124
                          · linarith only [h0, h14114, h14118, h14124, h3, hlam]
                          · linarith only [h1, h14116, h14118, h14124, h3, hc24, hc45, hlam, hphi]
                      · linarith only [h1, h14111, h14116, h14118, h14121, h3, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h14054, h14108, h14118, hc12, hc23, hlam, hphi]
          · linarith only [h14054, h14108, h14111, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h14130 | h14130
        · linarith only [h0, h14130, h3, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h14132 | h14132
          · rcases m.htr 0 3 5 (by decide) (by decide) with h14133 | h14133
            · linarith only [h1, h14133, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14135 | h14135
              · linarith only [h1, h14132, h14135, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14137 | h14137
                · linarith only [h0, h14054, h14137, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14139 | h14139
                  · linarith only [h0, h14108, h14139, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14141 | h14141
                    · linarith only [h0, h14130, h14141, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14143 | h14143
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14144 | h14144
                        · linarith only [h1, h14133, h14144, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h14146 | h14146
                          · linarith only [h14135, h14146, h2, h3, hlam]
                          · linarith only [h1, h14143, h14146, h3, hc34, hc45, hlam, hphi]
                      · linarith only [h14132, h14133, h14143, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h14150 | h14150
            · linarith only [h1, h14150, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14152 | h14152
              · linarith only [h14152, h2, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14154 | h14154
                · linarith only [h0, h14054, h14154, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14156 | h14156
                  · linarith only [h1, h14108, h14132, h14154, h14156, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14158 | h14158
                    · linarith only [h0, h14130, h14158, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14160 | h14160
                      · linarith only [h1, h14132, h14160, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14162 | h14162
                        · linarith only [h1, h14054, h14150, h14158, h14162, h3, hc02, hc25, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h14164 | h14164
                          · linarith only [h14152, h14162, h14164, h2, h3, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h14166 | h14166
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14167 | h14167
                              · linarith only [h0, h14162, h14167, h3, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h14054, h14132, h14166, h14167, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14170 | h14170
                              · linarith only [h0, h14054, h14150, h14166, h14170, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h14172 | h14172
                                · linarith only [h14154, h14160, h14164, h14172, h2, h3, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h14174 | h14174
                                  · linarith only [h0, h14054, h14166, h14172, h14174, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h14054, h14166, h14174, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 28996000 in
set_option maxHeartbeats 28996000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s2 m hb0 hb2 hb3 hb5 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h14177 | h14177
    · rcases m.htr 0 2 3 (by decide) (by decide) with h14178 | h14178
      · rcases m.htr 0 2 4 (by decide) (by decide) with h14179 | h14179
        · linarith only [h0, h14179, h2, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h14181 | h14181
          · rcases m.htr 0 3 4 (by decide) (by decide) with h14182 | h14182
            · linarith only [h1, h14182, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h14184 | h14184
              · rcases m.htr 0 4 5 (by decide) (by decide) with h14185 | h14185
                · rcases m.htr 1 2 3 (by decide) (by decide) with h14186 | h14186
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h14187 | h14187
                    · linarith only [h0, h14179, h14187, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h14189 | h14189
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h14190 | h14190
                        · linarith only [h1, h14182, h14190, h2, hlam]
                        · linarith only [h0, h14186, h14190, h2, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h14181, h14186, h14189, h2, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h14178, h14179, h14186, hc12, hc24, hlam, hphi]
                · linarith only [h1, h14184, h14185, h2, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h14196 | h14196
                · rcases m.htr 1 2 3 (by decide) (by decide) with h14197 | h14197
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h14198 | h14198
                    · linarith only [h0, h14179, h14181, h14198, hc01, hc25, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h14200 | h14200
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h14201 | h14201
                        · linarith only [h1, h14182, h14201, hlam]
                        · linarith only [h0, h14197, h14201, h2, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h14181, h14197, h14200, h2, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h14178, h14179, h14197, hc12, hc24, hlam, hphi]
                · linarith only [h0, h14181, h14196, h2, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h14207 | h14207
            · linarith only [h1, h14207, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h14209 | h14209
              · linarith only [h14178, h14181, h14209, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h14211 | h14211
                · rcases m.htr 1 2 3 (by decide) (by decide) with h14212 | h14212
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h14213 | h14213
                    · linarith only [h0, h14179, h14213, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h14215 | h14215
                      · linarith only [h0, h14181, h14215, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h14217 | h14217
                        · linarith only [h14177, h14207, h14212, h14215, h14217, h2, hlam]
                        · linarith only [h14177, h14212, h14215, h14217, h2, hc23, hc34, hlam, hphi]
                  · linarith only [h14178, h14181, h14212, hc12, hc25, hlam, hphi]
                · linarith only [h14177, h14211, h2, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h14222 | h14222
        · linarith only [h0, h14222, h2, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h14224 | h14224
          · rcases m.htr 0 3 4 (by decide) (by decide) with h14225 | h14225
            · linarith only [h1, h14225, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h14227 | h14227
              · rcases m.htr 0 4 5 (by decide) (by decide) with h14228 | h14228
                · rcases m.htr 1 2 3 (by decide) (by decide) with h14229 | h14229
                  · linarith only [h0, h14178, h14229, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h14231 | h14231
                    · linarith only [h0, h14222, h14231, h2, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h14233 | h14233
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h14234 | h14234
                        · linarith only [h1, h14225, h14227, h14234, h2, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h14236 | h14236
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h14237 | h14237
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14238 | h14238
                              · linarith only [h1, h14229, h14233, h14234, h14238, h2, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h14240 | h14240
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h14241 | h14241
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h14242 | h14242
                                    · rcases h0bigk with h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c | h14243c
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [hlam, p14243_0]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [h0, h14231, h14233, h14238, h14240, h14242, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14243_1]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [h0, h14178, h14231, h14233, h14238, h14240, h14242, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14243_1]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [h2, hlam, p14243_1]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        rcases p14243_3 (m.d 0 1) (by simp) with h14248 | h14248
                                        · rcases p14243_3 (m.d 0 2) (by simp) with h14249 | h14249
                                          · linarith only [h0, h14249, hlam]
                                          · linarith only [h14224, h14249, hlam]
                                        · linarith only [h14177, h14248, hlam]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [h0, hlam, p14243_0]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [hlam, p14243_0]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [h14178, hlam, p14243_0]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [h14222, hlam, p14243_1]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [h14177, h14178, h14238, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14243_1]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [h1, hlam, p14243_1]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [h1, h14231, h14238, h2, hc02, hc34, hlam, hphi, ht23, p14243_1]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [hlam, p14243_0]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [h14225, hlam, p14243_1]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        rcases p14243_3 (m.d 0 1) (by simp) with h14262 | h14262
                                        · rcases p14243_3 (m.d 0 2) (by simp) with h14263 | h14263
                                          · linarith only [h14178, h14263, hlam]
                                          · linarith only [h14224, h14263, hlam]
                                        · linarith only [h14177, h14262, hlam]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [h0, h14231, h14233, h14238, h14240, h14242, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14243_1]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        rcases p14243_3 (m.d 0 1) (by simp) with h14268 | h14268
                                        · linarith only [h14268, h2, hlam]
                                        · linarith only [h0, h14268, hlam]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        rcases p14243_3 (m.d 0 1) (by simp) with h14271 | h14271
                                        · linarith only [h14271, h2, hlam]
                                        · linarith only [h1, h14271, hlam]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [hlam, p14243_0]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        rcases p14243_3 (m.d 0 1) (by simp) with h14275 | h14275
                                        · linarith only [h14275, h2, hlam]
                                        · linarith only [h14177, h14275, hlam]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [h14177, hlam, p14243_0]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [h14224, hlam, p14243_1]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [h14227, hlam, p14243_0]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [h14228, hlam, p14243_1]
                                      · have p14243_0 := h14243c.1
                                        have p14243_1 := h14243c.2.1
                                        have p14243_2 := h14243c.2.2.1
                                        have p14243_3 := h14243c.2.2.2
                                        linarith only [hlam, p14243_0]
                                    · linarith only [h1, h14229, h14231, h14238, h14242, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h1, h14177, h14229, h14231, h14233, h14237, h14240, h14241, h2, hc05, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h0, h14178, h14227, h14233, h14240, hc03, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h1, h14229, h14233, h14237, h2, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h1, h14227, h14229, h14233, h14236, h2, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h1, h14178, h14224, h14231, h14233, h2, hc12, hc24, hlam, hphi]
                · linarith only [h1, h14178, h14224, h14228, h2, hlam]
              · linarith only [h14178, h14224, h14227, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h14291 | h14291
            · linarith only [h1, h14291, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h14293 | h14293
              · rcases m.htr 0 4 5 (by decide) (by decide) with h14294 | h14294
                · rcases m.htr 1 2 3 (by decide) (by decide) with h14295 | h14295
                  · linarith only [h0, h14178, h14295, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h14297 | h14297
                    · linarith only [h1, h14222, h14295, h14297, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h14299 | h14299
                      · linarith only [h0, h14224, h14299, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h14301 | h14301
                        · linarith only [h1, h14291, h14297, h14301, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h14303 | h14303
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h14304 | h14304
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14305 | h14305
                              · linarith only [h0, h14301, h14305, h2, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h14307 | h14307
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h14308 | h14308
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h14309 | h14309
                                    · rcases h0bigk with h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c | h14310c
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [hlam, p14310_0]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [h0, h14297, h2, hc12, hc24, hlam, hphi, p14310_1]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [h1, h14297, h14303, h14309, h2, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14310_1]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [h2, hlam, p14310_1]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [h0, h14224, h14297, h2, hc12, hc24, hlam, hphi, p14310_1]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [h0, hlam, p14310_0]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [hlam, p14310_0]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [h14178, hlam, p14310_0]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [h14222, hlam, p14310_1]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [h14224, hlam, p14310_0]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [h1, hlam, p14310_1]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [h0, h1, h14297, h2, hc12, hc24, hlam, hphi, p14310_1]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [hlam, p14310_0]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [h14291, hlam, p14310_1]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [h0, h1, h14224, h14297, h2, hc12, hc24, hlam, hphi, p14310_1]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [h1, h14303, h14309, hc04, hc45, hlam, hphi, ht0b, ht5b, p14310_1]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        rcases p14310_3 (m.d 0 1) (by simp) with h14327 | h14327
                                        · linarith only [h14327, h2, hlam]
                                        · linarith only [h0, h14327, hlam]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        rcases p14310_3 (m.d 0 1) (by simp) with h14330 | h14330
                                        · linarith only [h14330, h2, hlam]
                                        · linarith only [h1, h14330, hlam]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [hlam, p14310_0]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        rcases p14310_3 (m.d 0 1) (by simp) with h14334 | h14334
                                        · linarith only [h14334, h2, hlam]
                                        · linarith only [h14177, h14334, hlam]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [h14177, hlam, p14310_0]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [h0, h14177, h14297, h14305, h2, hc12, hc34, hlam, hphi, ht23, p14310_1]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [h14293, hlam, p14310_0]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [h14294, hlam, p14310_1]
                                      · have p14310_0 := h14310c.1
                                        have p14310_1 := h14310c.2.1
                                        have p14310_2 := h14310c.2.2.1
                                        have p14310_3 := h14310c.2.2.2
                                        linarith only [hlam, p14310_0]
                                    · linarith only [h0, h14297, h14305, h14309, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h1, h14297, h14303, h14304, h14308, h2, hc15, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h1, h14303, h14307, h2, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h1, h14293, h14294, h14303, h14304, h2, hc03, hc35, hlam, hphi, ht0b, ht5b]
                          · linarith only [h1, h14293, h14295, h14301, h14303, h2, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h14293, h14294, h2, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h14348 | h14348
                · rcases m.htr 1 2 3 (by decide) (by decide) with h14349 | h14349
                  · linarith only [h0, h14178, h14349, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h14351 | h14351
                    · linarith only [h0, h14222, h14351, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h14353 | h14353
                      · linarith only [h0, h14224, h14353, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h14355 | h14355
                        · linarith only [h1, h14291, h14355, h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h14357 | h14357
                          · linarith only [h1, h14293, h14357, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h14359 | h14359
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14360 | h14360
                              · linarith only [h14177, h14349, h14355, h14357, h14360, h2, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h14362 | h14362
                                · linarith only [h1, h14293, h14349, h14360, h14362, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h14364 | h14364
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h14365 | h14365
                                    · rcases h0bigk with h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c | h14366c
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [hlam, p14366_0]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [h0, h14351, h2, hc12, hc24, hlam, hphi, p14366_1]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [h1, h14349, h14351, h2, hc12, hc24, hlam, hphi, p14366_1]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [h2, hlam, p14366_1]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [h14177, h14349, h14351, h14357, h2, hc12, hc24, hlam, hphi, p14366_1]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [h0, hlam, p14366_0]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [hlam, p14366_0]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [h14178, hlam, p14366_0]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [h14222, hlam, p14366_1]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [h14224, hlam, p14366_0]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [h1, hlam, p14366_1]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [h0, h1, h14351, h2, hc12, hc24, hlam, hphi, p14366_1]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [hlam, p14366_0]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [h14291, hlam, p14366_1]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [h14293, hlam, p14366_1]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [h0, h14351, h2, hc12, hc24, hlam, hphi, p14366_1]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        rcases p14366_3 (m.d 0 1) (by simp) with h14383 | h14383
                                        · linarith only [h14383, h2, hlam]
                                        · linarith only [h0, h14383, hlam]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        rcases p14366_3 (m.d 0 1) (by simp) with h14386 | h14386
                                        · linarith only [h14386, h2, hlam]
                                        · linarith only [h1, h14386, hlam]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [hlam, p14366_0]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        rcases p14366_3 (m.d 0 1) (by simp) with h14390 | h14390
                                        · linarith only [h14390, h2, hlam]
                                        · linarith only [h14177, h14390, hlam]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [h14177, hlam, p14366_0]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [h0, h14177, h14351, h14360, h2, hc12, hc34, hlam, hphi, ht23, p14366_1]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [h14177, h14351, h14360, h2, hc03, hc34, hlam, hphi, p14366_1]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [h14348, hlam, p14366_1]
                                      · have p14366_0 := h14366c.1
                                        have p14366_1 := h14366c.2.1
                                        have p14366_2 := h14366c.2.2.1
                                        have p14366_3 := h14366c.2.2.2
                                        linarith only [hlam, p14366_0]
                                    · linarith only [h0, h14351, h14360, h14365, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h14177, h14351, h14359, h14364, h2, hlam]
                            · linarith only [h14177, h14349, h14357, h14359, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h14177, h14348, h2, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h14402 | h14402
      · rcases m.htr 0 2 4 (by decide) (by decide) with h14403 | h14403
        · linarith only [h0, h14403, h2, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h14405 | h14405
          · linarith only [h0, h14177, h14405, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h14407 | h14407
            · linarith only [h1, h14407, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h14409 | h14409
              · linarith only [h0, h14177, h14402, h14409, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h14411 | h14411
                · rcases m.htr 1 2 3 (by decide) (by decide) with h14412 | h14412
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h14413 | h14413
                    · linarith only [h0, h14403, h14413, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h14415 | h14415
                      · linarith only [h0, h14177, h14405, h14415, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h14417 | h14417
                        · linarith only [h0, h14177, h14407, h14411, h14412, h14417, hlam]
                        · linarith only [h0, h14412, h14417, h2, hc23, hc34, hlam, hphi]
                  · linarith only [h14402, h14403, h14412, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h14421 | h14421
                  · linarith only [h0, h14411, h14421, h2, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h14402, h14411, h14421, h2, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h14424 | h14424
        · linarith only [h1, h14402, h14424, h2, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h14426 | h14426
          · linarith only [h1, h14177, h14402, h14426, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h14428 | h14428
            · linarith only [h1, h14428, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h14430 | h14430
              · linarith only [h1, h14177, h14430, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h14432 | h14432
                · rcases m.htr 1 2 3 (by decide) (by decide) with h14433 | h14433
                  · linarith only [h0, h14402, h14433, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h14435 | h14435
                    · linarith only [h0, h14177, h14424, h14432, h14435, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h14437 | h14437
                      · linarith only [h0, h14426, h14435, h14437, h2, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h14439 | h14439
                        · linarith only [h1, h14428, h14435, h14439, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h14441 | h14441
                          · linarith only [h1, h14177, h14430, h14441, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h14443 | h14443
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14444 | h14444
                              · linarith only [h0, h14177, h14439, h14443, h14444, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h14446 | h14446
                                · linarith only [h1, h14177, h14433, h14441, h14444, h14446, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h14448 | h14448
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h14449 | h14449
                                    · rcases h0bigk with h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c | h14450c
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [hlam, p14450_0]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [h0, h14177, h14437, hc12, hc25, hlam, hphi, p14450_1]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [h0, h14177, h14402, h14437, hc12, hc25, hlam, hphi, p14450_1]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [h2, hlam, p14450_1]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [h14177, hlam, p14450_1]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [h0, hlam, p14450_0]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [hlam, p14450_0]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [h14402, hlam, p14450_0]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [h14424, hlam, p14450_1]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [h14426, hlam, p14450_0]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [h1, hlam, p14450_1]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [h0, h1, h14177, h14437, hc12, hc25, hlam, hphi, p14450_1]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [hlam, p14450_0]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [h14428, hlam, p14450_1]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [h14430, hlam, p14450_1]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [h0, h14424, h14444, hc12, hc34, hlam, hphi, ht23, p14450_1]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        rcases p14450_3 (m.d 0 1) (by simp) with h14467 | h14467
                                        · linarith only [h14467, h2, hlam]
                                        · linarith only [h0, h14467, hlam]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        rcases p14450_3 (m.d 0 1) (by simp) with h14470 | h14470
                                        · linarith only [h14470, h2, hlam]
                                        · linarith only [h1, h14470, hlam]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [hlam, p14450_0]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [h1, h14177, h14433, h14435, h14444, h2, hc12, hc34, hlam, hphi, ht23, p14450_1]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [h1, h14177, h14433, h14435, h14443, h14444, hc12, hc34, hlam, hphi, ht23, p14450_1]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        rcases p14450_3 (m.d 0 1) (by simp) with h14476 | h14476
                                        · linarith only [h14177, h14476, hlam]
                                        · linarith only [h0, h14476, hlam]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        rcases p14450_3 (m.d 0 1) (by simp) with h14479 | h14479
                                        · linarith only [h14177, h14479, hlam]
                                        · linarith only [h1, h14479, hlam]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [h14432, hlam, p14450_1]
                                      · have p14450_0 := h14450c.1
                                        have p14450_1 := h14450c.2.1
                                        have p14450_2 := h14450c.2.2.1
                                        have p14450_3 := h14450c.2.2.2
                                        linarith only [hlam, p14450_0]
                                    · linarith only [h14432, h14435, h14444, h14449, h2, hlam]
                                  · linarith only [h14432, h14435, h14448, h2, hlam]
                            · linarith only [h14432, h14443, h2, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h14487 | h14487
                  · linarith only [h0, h14432, h14487, h2, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h14489 | h14489
                    · linarith only [h1, h14432, h14487, h14489, h2, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h14491 | h14491
                      · linarith only [h0, h14426, h14491, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h14493 | h14493
                        · linarith only [h0, h1, h14402, h14428, h14493, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h14495 | h14495
                          · linarith only [h1, h14430, h14495, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h14497 | h14497
                            · linarith only [h1, h14432, h14493, h14497, h2, hc13, hc34, hlam, hphi]
                            · linarith only [h1, h14487, h14497, h2, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 31062000 in
set_option maxHeartbeats 31062000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s1 m hb0 hb2 hb3 hb5 h0 h1

end R2N4
