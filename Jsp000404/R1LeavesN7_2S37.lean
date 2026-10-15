import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11722000 in
set_option maxHeartbeats 11722000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h20411 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h24656 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  rcases m.htr 0 4 5 (by decide) (by decide) with h24657 | h24657
  · rcases m.htr 1 2 3 (by decide) (by decide) with h24658 | h24658
    · rcases m.htr 1 2 4 (by decide) (by decide) with h24659 | h24659
      · rcases m.htr 1 2 5 (by decide) (by decide) with h24660 | h24660
        · rcases m.htr 1 3 4 (by decide) (by decide) with h24661 | h24661
          · rcases m.htr 1 3 5 (by decide) (by decide) with h24662 | h24662
            · rcases m.htr 1 4 5 (by decide) (by decide) with h24663 | h24663
              · rcases m.htr 2 3 4 (by decide) (by decide) with h24664 | h24664
                · linarith only [h20408, h20411, h24664, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h24666 | h24666
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h24667 | h24667
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h24668 | h24668
                      · rcases h0bigk with h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c | h24669c
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [hlam, p24669_0]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [h0, hlam, p24669_1]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [h14396, hlam, p24669_0]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [h16915, hlam, p24669_1]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [h18815, hlam, p24669_1]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          rcases p24669_3 (m.d 0 1) (by simp) with h24675 | h24675
                          · linarith only [h0, h24675, hlam]
                          · rcases p24669_3 (m.d 0 2) (by simp) with h24677 | h24677
                            · rcases p24669_3 (m.d 0 3) (by simp) with h24678 | h24678
                              · linarith only [h20408, h24678, hlam]
                              · linarith only [h14396, h24678, hlam]
                            · linarith only [h0, h24677, hlam]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [hlam, p24669_0]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          rcases p24669_3 (m.d 0 1) (by simp) with h24683 | h24683
                          · linarith only [h0, h24683, hlam]
                          · rcases p24669_3 (m.d 0 2) (by simp) with h24685 | h24685
                            · rcases p24669_3 (m.d 0 3) (by simp) with h24686 | h24686
                              · linarith only [h20408, h24686, hlam]
                              · rcases p24669_3 (m.d 0 4) (by simp) with h24688 | h24688
                                · linarith only [h20409, h24688, hlam]
                                · linarith only [h20411, h24688, hlam]
                            · linarith only [h20408, h24685, hlam]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          rcases p24669_3 (m.d 0 1) (by simp) with h24692 | h24692
                          · linarith only [h0, h24692, hlam]
                          · rcases p24669_3 (m.d 0 2) (by simp) with h24694 | h24694
                            · rcases p24669_3 (m.d 0 3) (by simp) with h24695 | h24695
                              · linarith only [h20408, h24695, hlam]
                              · rcases p24669_3 (m.d 0 4) (by simp) with h24697 | h24697
                                · linarith only [h20409, h24697, hlam]
                                · rcases p24669_3 (m.d 0 5) (by simp) with h24699 | h24699
                                  · linarith only [h20410, h24699, hlam]
                                  · rcases h2bigk with h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c | h24701c
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [hlam, p24701_0]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [h0, hlam, p24701_1]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      rcases p24701_3 (m.d 0 2) (by simp) with h24704 | h24704
                                      · rcases p24701_3 (m.d 1 2) (by simp) with h24705 | h24705
                                        · rcases p24701_3 (m.d 2 3) (by simp) with h24706 | h24706
                                          · linarith only [h24706, hlam, p24701_0]
                                          · rcases p24701_3 (m.d 2 4) (by simp) with h24708 | h24708
                                            · linarith only [h20409, h24708, hlam]
                                            · linarith only [h24664, h24708, hlam]
                                        · linarith only [h24658, h24705, hlam]
                                      · linarith only [h24704, hlam, p24701_0]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      rcases p24701_3 (m.d 0 2) (by simp) with h24713 | h24713
                                      · rcases p24701_3 (m.d 1 2) (by simp) with h24714 | h24714
                                        · rcases p24701_3 (m.d 2 3) (by simp) with h24715 | h24715
                                          · linarith only [h20408, h24715, hlam]
                                          · rcases p24701_3 (m.d 2 4) (by simp) with h24717 | h24717
                                            · linarith only [h24717, hlam, p24701_0]
                                            · rcases p24701_3 (m.d 2 5) (by simp) with h24719 | h24719
                                              · linarith only [h20410, h24719, hlam]
                                              · rcases h3bigk with h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c | h24721c
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [hlam, p24721_0]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h14396, hlam, p24721_1]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h0, h20411, h24666, h24668, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24669_1, p24721_1]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h20411, hlam, p24721_0]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h0, h20411, h24668, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24669_1, p24721_1]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h14396, h24658, hc01, hc12, hlam, hphi, p24721_1]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [hlam, p24721_0]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h24658, h24666, h24668, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24721_1]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h20411, h24658, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24721_1]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  rcases p24721_3 (m.d 0 3) (by simp) with h24731 | h24731
                                                  · linarith only [h14396, h24731, hlam]
                                                  · linarith only [h24656, h24731, hlam]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h20408, hlam, p24721_0]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h24658, hlam, p24721_0]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [hlam, p24721_0]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h24664, hlam, p24721_0]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h20408, h20411, h24661, h24668, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p24721_1]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [hc03, hc34, hlam, hphi, p24721_1]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h24661, hlam, p24721_0]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h24658, h24661, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24721_1]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [hlam, p24721_0]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h24658, h24661, h24668, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24721_1]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h24656, hlam, p24721_0]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h24662, hlam, p24721_0]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h24666, hlam, p24721_0]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [h24668, hlam, p24721_0]
                                                · have p24721_0 := h24721c.1
                                                  have p24721_1 := h24721c.2.1
                                                  have p24721_2 := h24721c.2.2.1
                                                  have p24721_3 := h24721c.2.2.2
                                                  linarith only [hlam, p24721_0]
                                        · linarith only [h24659, h24714, hlam]
                                      · linarith only [h24713, hlam, p24701_0]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      rcases p24701_3 (m.d 0 2) (by simp) with h24751 | h24751
                                      · rcases p24701_3 (m.d 1 2) (by simp) with h24752 | h24752
                                        · rcases p24701_3 (m.d 2 3) (by simp) with h24753 | h24753
                                          · linarith only [h20408, h24753, hlam]
                                          · linarith only [h24666, h24753, hlam]
                                        · linarith only [h24660, h24752, hlam]
                                      · linarith only [h24751, hlam, p24701_0]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p24669_1, p24701_1]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [hlam, p24701_0]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      rcases p24701_3 (m.d 0 2) (by simp) with h24760 | h24760
                                      · linarith only [h0, h24760, hlam]
                                      · linarith only [h20408, h24760, hlam]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      rcases p24701_3 (m.d 0 2) (by simp) with h24763 | h24763
                                      · linarith only [h0, h24763, hlam]
                                      · linarith only [h20409, h24763, hlam]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      rcases p24701_3 (m.d 0 2) (by simp) with h24766 | h24766
                                      · linarith only [h0, h24766, hlam]
                                      · linarith only [h20410, h24766, hlam]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [h20408, hlam, p24701_0]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [h24658, hlam, p24701_0]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [hlam, p24701_0]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [h24664, hlam, p24701_0]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [h20409, h24664, hc02, hc25, hlam, hphi, ht0b, ht5b, p24669_1, p24701_1]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [h20409, hlam, p24701_0]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [h24659, hlam, p24701_0]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [h20409, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24669_1, p24701_1]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [hlam, p24701_0]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [h0, h20409, h24666, h24668, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24669_1, p24701_1]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [h20410, hlam, p24701_0]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [h24660, hlam, p24701_0]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [h24666, hlam, p24701_1]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [h24667, hlam, p24701_0]
                                    · have p24701_0 := h24701c.1
                                      have p24701_1 := h24701c.2.1
                                      have p24701_2 := h24701c.2.2.1
                                      have p24701_3 := h24701c.2.2.2
                                      linarith only [hlam, p24701_0]
                            · linarith only [h20409, h24694, hlam]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          rcases p24669_3 (m.d 0 1) (by simp) with h24785 | h24785
                          · linarith only [h0, h24785, hlam]
                          · rcases p24669_3 (m.d 0 2) (by simp) with h24787 | h24787
                            · rcases p24669_3 (m.d 0 3) (by simp) with h24788 | h24788
                              · linarith only [h20408, h24788, hlam]
                              · linarith only [h24656, h24788, hlam]
                            · linarith only [h20410, h24787, hlam]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [h20411, h24658, h24661, hc01, hc12, hlam, hphi, p24669_1]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [h20408, hlam, p24669_1]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [hlam, p24669_0]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [h20411, hlam, p24669_1]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [h18815, h20411, h24658, h24661, hc01, hc12, hlam, hphi, p24669_1]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [h20411, h24658, h24661, hc01, hc12, hlam, hphi, p24669_1]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [h20409, hlam, p24669_0]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [h14396, h20411, h24658, h24661, hc01, hc12, hlam, hphi, p24669_1]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [hlam, p24669_0]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [h18815, h20411, h24658, h24661, hc01, hc12, hlam, hphi, p24669_1]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [h20411, h24656, h24658, h24661, hc01, hc12, hlam, hphi, p24669_1]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [h20410, hlam, p24669_1]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [h24656, hlam, p24669_0]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [h24657, hlam, p24669_1]
                        · have p24669_0 := h24669c.1
                          have p24669_1 := h24669c.2.1
                          have p24669_2 := h24669c.2.2.1
                          have p24669_3 := h24669c.2.2.2
                          linarith only [hlam, p24669_0]
                      · linarith only [h20411, h24657, h24668, hlam]
                    · linarith only [h20411, h24656, h24657, h24658, h24661, h24664, h24666, h24667, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h20411, h24656, h24658, h24661, h24666, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h16915, h20411, h24656, h24657, h24658, h24661, h24663, hc01, hc12, hlam, hphi]
            · linarith only [h20411, h24656, h24661, h24662, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h24812 | h24812
            · rcases m.htr 1 4 5 (by decide) (by decide) with h24813 | h24813
              · rcases m.htr 2 3 4 (by decide) (by decide) with h24814 | h24814
                · linarith only [h18815, h24661, h24812, h24814, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h24816 | h24816
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h24817 | h24817
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h24818 | h24818
                      · rcases h0bigk with h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [hlam, p24819_0]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [h0, hlam, p24819_1]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [h14396, hlam, p24819_0]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [h16915, hlam, p24819_1]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [h18815, hlam, p24819_1]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          rcases p24819_3 (m.d 0 1) (by simp) with h24825 | h24825
                          · linarith only [h0, h24825, hlam]
                          · rcases p24819_3 (m.d 0 2) (by simp) with h24827 | h24827
                            · rcases p24819_3 (m.d 0 3) (by simp) with h24828 | h24828
                              · linarith only [h20408, h24828, hlam]
                              · linarith only [h14396, h24828, hlam]
                            · linarith only [h0, h24827, hlam]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [hlam, p24819_0]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          rcases p24819_3 (m.d 0 1) (by simp) with h24833 | h24833
                          · linarith only [h0, h24833, hlam]
                          · rcases p24819_3 (m.d 0 2) (by simp) with h24835 | h24835
                            · rcases p24819_3 (m.d 0 3) (by simp) with h24836 | h24836
                              · linarith only [h20408, h24836, hlam]
                              · rcases p24819_3 (m.d 0 4) (by simp) with h24838 | h24838
                                · linarith only [h20409, h24838, hlam]
                                · linarith only [h20411, h24838, hlam]
                            · linarith only [h20408, h24835, hlam]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          rcases p24819_3 (m.d 0 1) (by simp) with h24842 | h24842
                          · linarith only [h0, h24842, hlam]
                          · rcases p24819_3 (m.d 0 2) (by simp) with h24844 | h24844
                            · rcases p24819_3 (m.d 0 3) (by simp) with h24845 | h24845
                              · linarith only [h20408, h24845, hlam]
                              · rcases p24819_3 (m.d 0 4) (by simp) with h24847 | h24847
                                · linarith only [h20409, h24847, hlam]
                                · rcases p24819_3 (m.d 0 5) (by simp) with h24849 | h24849
                                  · linarith only [h20410, h24849, hlam]
                                  · rcases h2bigk with h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c | h24851c
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [hlam, p24851_0]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [h0, hlam, p24851_1]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      rcases p24851_3 (m.d 0 2) (by simp) with h24854 | h24854
                                      · rcases p24851_3 (m.d 1 2) (by simp) with h24855 | h24855
                                        · rcases p24851_3 (m.d 2 3) (by simp) with h24856 | h24856
                                          · linarith only [h24856, hlam, p24851_0]
                                          · rcases p24851_3 (m.d 2 4) (by simp) with h24858 | h24858
                                            · linarith only [h20409, h24858, hlam]
                                            · linarith only [h24814, h24858, hlam]
                                        · linarith only [h24658, h24855, hlam]
                                      · linarith only [h24854, hlam, p24851_0]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      rcases p24851_3 (m.d 0 2) (by simp) with h24863 | h24863
                                      · rcases p24851_3 (m.d 1 2) (by simp) with h24864 | h24864
                                        · rcases p24851_3 (m.d 2 3) (by simp) with h24865 | h24865
                                          · linarith only [h20408, h24865, hlam]
                                          · rcases p24851_3 (m.d 2 4) (by simp) with h24867 | h24867
                                            · linarith only [h24867, hlam, p24851_0]
                                            · rcases p24851_3 (m.d 2 5) (by simp) with h24869 | h24869
                                              · linarith only [h20410, h24869, hlam]
                                              · rcases h3bigk with h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c | h24871c
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [hlam, p24871_0]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [h14396, hlam, p24871_1]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [h0, h20411, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24819_1, p24871_1]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [h20411, hlam, p24871_0]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [h0, h20411, h24818, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24819_1, p24871_1]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [h24661, hc03, hc34, hlam, hphi, p24871_1]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [hlam, p24871_0]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [h24661, h24816, h24818, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p24871_1]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [h24661, hlam, p24871_0]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [h24661, h24818, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p24871_1]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [h20408, hlam, p24871_0]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [h24658, hlam, p24871_0]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [hlam, p24871_0]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [h24814, hlam, p24871_0]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [h14396, h20408, h24661, h24818, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p24871_1]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [hc03, hc34, hlam, hphi, p24871_1]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [hc13, hc34, hlam, hphi, p24871_1]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [hc23, hc34, hlam, hphi, p24871_1]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [hlam, p24871_0]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  rcases p24871_3 (m.d 0 3) (by simp) with h24891 | h24891
                                                  · linarith only [h20411, h24891, hlam]
                                                  · linarith only [h24656, h24891, hlam]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [h24656, hlam, p24871_0]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [h24812, hlam, p24871_0]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [h24816, hlam, p24871_0]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [h24818, hlam, p24871_0]
                                                · have p24871_0 := h24871c.1
                                                  have p24871_1 := h24871c.2.1
                                                  have p24871_2 := h24871c.2.2.1
                                                  have p24871_3 := h24871c.2.2.2
                                                  linarith only [hlam, p24871_0]
                                        · linarith only [h24659, h24864, hlam]
                                      · linarith only [h24863, hlam, p24851_0]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      rcases p24851_3 (m.d 0 2) (by simp) with h24901 | h24901
                                      · rcases p24851_3 (m.d 1 2) (by simp) with h24902 | h24902
                                        · rcases p24851_3 (m.d 2 3) (by simp) with h24903 | h24903
                                          · linarith only [h20408, h24903, hlam]
                                          · linarith only [h24816, h24903, hlam]
                                        · linarith only [h24660, h24902, hlam]
                                      · linarith only [h24901, hlam, p24851_0]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p24819_1, p24851_1]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [hlam, p24851_0]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      rcases p24851_3 (m.d 0 2) (by simp) with h24910 | h24910
                                      · linarith only [h0, h24910, hlam]
                                      · linarith only [h20408, h24910, hlam]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      rcases p24851_3 (m.d 0 2) (by simp) with h24913 | h24913
                                      · linarith only [h0, h24913, hlam]
                                      · linarith only [h20409, h24913, hlam]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      rcases p24851_3 (m.d 0 2) (by simp) with h24916 | h24916
                                      · linarith only [h0, h24916, hlam]
                                      · linarith only [h20410, h24916, hlam]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [h20408, hlam, p24851_0]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [h24658, hlam, p24851_0]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [hlam, p24851_0]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [h24814, hlam, p24851_0]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [h20408, h20411, hc02, hc25, hlam, hphi, ht0b, ht5b, p24819_1, p24851_1]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [h20409, hlam, p24851_0]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [h24659, hlam, p24851_0]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [h0, h20409, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24819_1, p24851_1]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [hlam, p24851_0]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [h0, h20409, h24816, h24818, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24819_1, p24851_1]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [h20410, hlam, p24851_0]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [h24660, hlam, p24851_0]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [h24816, hlam, p24851_1]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [h24817, hlam, p24851_0]
                                    · have p24851_0 := h24851c.1
                                      have p24851_1 := h24851c.2.1
                                      have p24851_2 := h24851c.2.2.1
                                      have p24851_3 := h24851c.2.2.2
                                      linarith only [hlam, p24851_0]
                            · linarith only [h20409, h24844, hlam]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          rcases p24819_3 (m.d 0 1) (by simp) with h24935 | h24935
                          · linarith only [h0, h24935, hlam]
                          · rcases p24819_3 (m.d 0 2) (by simp) with h24937 | h24937
                            · rcases p24819_3 (m.d 0 3) (by simp) with h24938 | h24938
                              · linarith only [h20408, h24938, hlam]
                              · linarith only [h24656, h24938, hlam]
                            · linarith only [h20410, h24937, hlam]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [h20411, hc01, hc34, hlam, hphi, ht12, ht23, p24819_1]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [h20408, hlam, p24819_1]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [hlam, p24819_0]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [h20411, hlam, p24819_1]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [h18815, h20411, hc01, hc34, hlam, hphi, ht12, ht23, p24819_1]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          rcases p24819_3 (m.d 0 1) (by simp) with h24947 | h24947
                          · linarith only [h16915, h24947, hlam]
                          · rcases p24819_3 (m.d 0 2) (by simp) with h24949 | h24949
                            · rcases p24819_3 (m.d 0 3) (by simp) with h24950 | h24950
                              · linarith only [h20411, h24950, hlam]
                              · linarith only [h14396, h24950, hlam]
                            · linarith only [h0, h24949, hlam]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [h20409, hlam, p24819_0]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          rcases p24819_3 (m.d 0 1) (by simp) with h24955 | h24955
                          · linarith only [h16915, h24955, hlam]
                          · rcases p24819_3 (m.d 0 2) (by simp) with h24957 | h24957
                            · rcases p24819_3 (m.d 0 3) (by simp) with h24958 | h24958
                              · linarith only [h20411, h24958, hlam]
                              · rcases p24819_3 (m.d 0 4) (by simp) with h24960 | h24960
                                · rcases p24819_3 (m.d 0 5) (by simp) with h24961 | h24961
                                  · linarith only [h24657, h24961, hlam]
                                  · rcases h2bigk with h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c | h24963c
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [hlam, p24963_0]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [h0, hlam, p24963_1]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      rcases p24963_3 (m.d 0 2) (by simp) with h24966 | h24966
                                      · rcases p24963_3 (m.d 1 2) (by simp) with h24967 | h24967
                                        · rcases p24963_3 (m.d 2 3) (by simp) with h24968 | h24968
                                          · linarith only [h24968, hlam, p24963_0]
                                          · rcases p24963_3 (m.d 2 4) (by simp) with h24970 | h24970
                                            · linarith only [h20409, h24970, hlam]
                                            · linarith only [h24814, h24970, hlam]
                                        · linarith only [h24658, h24967, hlam]
                                      · linarith only [h24966, hlam, p24963_0]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      rcases p24963_3 (m.d 0 2) (by simp) with h24975 | h24975
                                      · rcases p24963_3 (m.d 1 2) (by simp) with h24976 | h24976
                                        · rcases p24963_3 (m.d 2 3) (by simp) with h24977 | h24977
                                          · linarith only [h20408, h24977, hlam]
                                          · rcases p24963_3 (m.d 2 4) (by simp) with h24979 | h24979
                                            · linarith only [h24979, hlam, p24963_0]
                                            · rcases p24963_3 (m.d 2 5) (by simp) with h24981 | h24981
                                              · linarith only [h20410, h24981, hlam]
                                              · rcases h3bigk with h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c | h24983c
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [hlam, p24983_0]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [h14396, hlam, p24983_1]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [h16915, h24661, h24816, h24818, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p24819_1, p24983_1]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [h20411, hlam, p24983_0]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [h16915, h24661, h24818, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p24819_1, p24983_1]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [h24661, hc03, hc34, hlam, hphi, p24983_1]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [hlam, p24983_0]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [h24661, h24816, h24818, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p24983_1]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [h24661, hlam, p24983_0]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [h24661, h24818, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p24983_1]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [h20408, hlam, p24983_0]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [h24658, hlam, p24983_0]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [hlam, p24983_0]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [h24814, hlam, p24983_0]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [h14396, h20408, h24661, h24818, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p24983_1]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [hc03, hc34, hlam, hphi, p24983_1]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [hc13, hc34, hlam, hphi, p24983_1]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [hc23, hc34, hlam, hphi, p24983_1]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [hlam, p24983_0]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  rcases p24983_3 (m.d 0 3) (by simp) with h25003 | h25003
                                                  · linarith only [h20411, h25003, hlam]
                                                  · linarith only [h24656, h25003, hlam]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [h24656, hlam, p24983_0]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [h24812, hlam, p24983_0]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [h24816, hlam, p24983_0]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [h24818, hlam, p24983_0]
                                                · have p24983_0 := h24983c.1
                                                  have p24983_1 := h24983c.2.1
                                                  have p24983_2 := h24983c.2.2.1
                                                  have p24983_3 := h24983c.2.2.2
                                                  linarith only [hlam, p24983_0]
                                        · linarith only [h24659, h24976, hlam]
                                      · linarith only [h24975, hlam, p24963_0]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      rcases p24963_3 (m.d 0 2) (by simp) with h25013 | h25013
                                      · rcases p24963_3 (m.d 1 2) (by simp) with h25014 | h25014
                                        · rcases p24963_3 (m.d 2 3) (by simp) with h25015 | h25015
                                          · linarith only [h20408, h25015, hlam]
                                          · linarith only [h24816, h25015, hlam]
                                        · linarith only [h24660, h25014, hlam]
                                      · linarith only [h25013, hlam, p24963_0]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [h20408, h24816, h24818, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24963_1]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [hlam, p24963_0]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      rcases p24963_3 (m.d 0 2) (by simp) with h25022 | h25022
                                      · linarith only [h0, h25022, hlam]
                                      · linarith only [h20408, h25022, hlam]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      rcases p24963_3 (m.d 0 2) (by simp) with h25025 | h25025
                                      · linarith only [h0, h25025, hlam]
                                      · linarith only [h20409, h25025, hlam]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      rcases p24963_3 (m.d 0 2) (by simp) with h25028 | h25028
                                      · linarith only [h0, h25028, hlam]
                                      · linarith only [h20410, h25028, hlam]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [h20408, hlam, p24963_0]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [h24658, hlam, p24963_0]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [hlam, p24963_0]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [h24814, hlam, p24963_0]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [h16915, h20408, h24661, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p24819_1, p24963_1]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [h20409, hlam, p24963_0]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [h24659, hlam, p24963_0]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [h0, h20409, h24816, h24818, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24963_1]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [hlam, p24963_0]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      rcases p24963_3 (m.d 0 2) (by simp) with h25040 | h25040
                                      · rcases p24963_3 (m.d 1 2) (by simp) with h25041 | h25041
                                        · rcases p24963_3 (m.d 2 3) (by simp) with h25042 | h25042
                                          · linarith only [h24814, h25042, hlam]
                                          · linarith only [h24816, h25042, hlam]
                                        · linarith only [h24660, h25041, hlam]
                                      · linarith only [h20410, h25040, hlam]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [h20410, hlam, p24963_0]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [h24660, hlam, p24963_0]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [h24816, hlam, p24963_1]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [h24817, hlam, p24963_0]
                                    · have p24963_0 := h24963c.1
                                      have p24963_1 := h24963c.2.1
                                      have p24963_2 := h24963c.2.2.1
                                      have p24963_3 := h24963c.2.2.2
                                      linarith only [hlam, p24963_0]
                                · linarith only [h20411, h24960, hlam]
                            · linarith only [h20408, h24957, hlam]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [hlam, p24819_0]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          rcases p24819_3 (m.d 0 1) (by simp) with h25055 | h25055
                          · linarith only [h16915, h25055, hlam]
                          · rcases p24819_3 (m.d 0 2) (by simp) with h25057 | h25057
                            · rcases p24819_3 (m.d 0 3) (by simp) with h25058 | h25058
                              · linarith only [h20411, h25058, hlam]
                              · linarith only [h24656, h25058, hlam]
                            · linarith only [h20410, h25057, hlam]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [h20411, h24656, hc01, hc34, hlam, hphi, ht12, ht23, p24819_1]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [h20410, hlam, p24819_1]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [h24656, hlam, p24819_0]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [h24657, hlam, p24819_1]
                        · have p24819_0 := h24819c.1
                          have p24819_1 := h24819c.2.1
                          have p24819_2 := h24819c.2.2.1
                          have p24819_3 := h24819c.2.2.2
                          linarith only [hlam, p24819_0]
                      · linarith only [h14396, h24661, h24818, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h24814, h24816, h24817, hlam]
                  · linarith only [h14396, h24656, h24661, h24816, hc23, hc34, hlam, hphi]
              · linarith only [h16915, h24657, h24813, hlam]
            · linarith only [h14396, h24656, h24812, hlam]
        · linarith only [h0, h20410, h24660, hlam]
      · linarith only [h0, h20409, h24659, hlam]
    · linarith only [h0, h20408, h24658, hlam]
  · linarith only [h20411, h24656, h24657, hlam]

set_option maxHeartbeats 11722000 in
set_option maxHeartbeats 11722000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h20411 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h24656 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h25076 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h25077 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25078 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25079 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25080 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  rcases m.htr 1 3 5 (by decide) (by decide) with h25081 | h25081
  · rcases m.htr 1 4 5 (by decide) (by decide) with h25082 | h25082
    · rcases m.htr 2 3 4 (by decide) (by decide) with h25083 | h25083
      · linarith only [h20408, h20411, h25083, hlam]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h25085 | h25085
        · linarith only [h20408, h24656, h25085, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h25087 | h25087
          · rcases m.htr 3 4 5 (by decide) (by decide) with h25088 | h25088
            · rcases h0bigk with h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c | h25089c
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [hlam, p25089_0]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [h0, hlam, p25089_1]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [h14396, hlam, p25089_0]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [h16915, hlam, p25089_1]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [h18815, hlam, p25089_1]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                rcases p25089_3 (m.d 0 1) (by simp) with h25095 | h25095
                · linarith only [h0, h25095, hlam]
                · rcases p25089_3 (m.d 0 2) (by simp) with h25097 | h25097
                  · rcases p25089_3 (m.d 0 3) (by simp) with h25098 | h25098
                    · linarith only [h20408, h25098, hlam]
                    · linarith only [h14396, h25098, hlam]
                  · linarith only [h0, h25097, hlam]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [hlam, p25089_0]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                rcases p25089_3 (m.d 0 1) (by simp) with h25103 | h25103
                · linarith only [h0, h25103, hlam]
                · rcases p25089_3 (m.d 0 2) (by simp) with h25105 | h25105
                  · rcases p25089_3 (m.d 0 3) (by simp) with h25106 | h25106
                    · linarith only [h20408, h25106, hlam]
                    · rcases p25089_3 (m.d 0 4) (by simp) with h25108 | h25108
                      · linarith only [h20409, h25108, hlam]
                      · linarith only [h20411, h25108, hlam]
                  · linarith only [h20408, h25105, hlam]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                rcases p25089_3 (m.d 0 1) (by simp) with h25112 | h25112
                · linarith only [h0, h25112, hlam]
                · rcases p25089_3 (m.d 0 2) (by simp) with h25114 | h25114
                  · rcases p25089_3 (m.d 0 3) (by simp) with h25115 | h25115
                    · linarith only [h20408, h25115, hlam]
                    · rcases p25089_3 (m.d 0 4) (by simp) with h25117 | h25117
                      · linarith only [h20409, h25117, hlam]
                      · rcases p25089_3 (m.d 0 5) (by simp) with h25119 | h25119
                        · linarith only [h20410, h25119, hlam]
                        · rcases h2bigk with h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c | h25121c
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [hlam, p25121_0]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [h0, hlam, p25121_1]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            rcases p25121_3 (m.d 0 2) (by simp) with h25124 | h25124
                            · rcases p25121_3 (m.d 1 2) (by simp) with h25125 | h25125
                              · rcases p25121_3 (m.d 2 3) (by simp) with h25126 | h25126
                                · linarith only [h25126, hlam, p25121_0]
                                · rcases p25121_3 (m.d 2 4) (by simp) with h25128 | h25128
                                  · linarith only [h20409, h25128, hlam]
                                  · linarith only [h25083, h25128, hlam]
                              · linarith only [h25077, h25125, hlam]
                            · linarith only [h25124, hlam, p25121_0]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            rcases p25121_3 (m.d 0 2) (by simp) with h25133 | h25133
                            · rcases p25121_3 (m.d 1 2) (by simp) with h25134 | h25134
                              · rcases p25121_3 (m.d 2 3) (by simp) with h25135 | h25135
                                · linarith only [h20408, h25135, hlam]
                                · rcases p25121_3 (m.d 2 4) (by simp) with h25137 | h25137
                                  · linarith only [h25137, hlam, p25121_0]
                                  · rcases p25121_3 (m.d 2 5) (by simp) with h25139 | h25139
                                    · linarith only [h20410, h25139, hlam]
                                    · rcases h3bigk with h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c | h25141c
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [hlam, p25141_0]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h14396, hlam, p25141_1]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h24656, h25080, h25088, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25141_1]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h20411, hlam, p25141_0]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h24656, hlam, p25141_0]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h14396, hc01, hc13, hlam, hphi, p25141_1]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [hlam, p25141_0]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        rcases p25141_3 (m.d 0 3) (by simp) with h25149 | h25149
                                        · linarith only [h14396, h25149, hlam]
                                        · linarith only [h20408, h25149, hlam]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h14396, h20411, h25077, hc01, hc12, hlam, hphi, p25141_1]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h14396, h24656, h25077, hc01, hc12, hlam, hphi, p25141_1]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h20408, hlam, p25141_0]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h25077, hlam, p25141_0]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [hlam, p25141_0]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h25083, hlam, p25141_0]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h25085, hlam, p25141_0]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h14396, h25080, hc01, hc14, hlam, hphi, p25141_1]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h25080, hlam, p25141_0]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h25077, h25080, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25141_1]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [hlam, p25141_0]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h14396, h24656, h25077, h25080, hc01, hc12, hlam, hphi, p25141_1]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h14396, h25081, hc01, hc15, hlam, hphi, p25141_1]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h25081, hlam, p25141_0]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h25077, h25081, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25141_1]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [h25088, hlam, p25141_0]
                                      · have p25141_0 := h25141c.1
                                        have p25141_1 := h25141c.2.1
                                        have p25141_2 := h25141c.2.2.1
                                        have p25141_3 := h25141c.2.2.2
                                        linarith only [hlam, p25141_0]
                              · linarith only [h25078, h25134, hlam]
                            · linarith only [h25133, hlam, p25121_0]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            rcases p25121_3 (m.d 0 2) (by simp) with h25171 | h25171
                            · rcases p25121_3 (m.d 1 2) (by simp) with h25172 | h25172
                              · rcases p25121_3 (m.d 2 3) (by simp) with h25173 | h25173
                                · linarith only [h20408, h25173, hlam]
                                · rcases p25121_3 (m.d 2 4) (by simp) with h25175 | h25175
                                  · linarith only [h20409, h25175, hlam]
                                  · linarith only [h25087, h25175, hlam]
                              · linarith only [h25079, h25172, hlam]
                            · linarith only [h25171, hlam, p25121_0]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p25089_1, p25121_1]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [hlam, p25121_0]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            rcases p25121_3 (m.d 0 2) (by simp) with h25182 | h25182
                            · linarith only [h0, h25182, hlam]
                            · linarith only [h20408, h25182, hlam]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            rcases p25121_3 (m.d 0 2) (by simp) with h25185 | h25185
                            · linarith only [h0, h25185, hlam]
                            · linarith only [h20409, h25185, hlam]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            rcases p25121_3 (m.d 0 2) (by simp) with h25188 | h25188
                            · linarith only [h0, h25188, hlam]
                            · linarith only [h20410, h25188, hlam]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [h20408, hlam, p25121_0]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [h25077, hlam, p25121_0]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [hlam, p25121_0]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [h25083, hlam, p25121_0]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [h25085, hlam, p25121_0]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [h20409, hlam, p25121_0]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [h25078, hlam, p25121_0]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [h20409, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25089_1, p25121_1]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [hlam, p25121_0]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [h0, h20409, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p25089_1, p25121_1]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [h20410, hlam, p25121_0]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [h25079, hlam, p25121_0]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [h0, h20410, h25076, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25089_1, p25121_1]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [h25087, hlam, p25121_0]
                          · have p25121_0 := h25121c.1
                            have p25121_1 := h25121c.2.1
                            have p25121_2 := h25121c.2.2.1
                            have p25121_3 := h25121c.2.2.2
                            linarith only [hlam, p25121_0]
                  · linarith only [h20409, h25114, hlam]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                rcases p25089_3 (m.d 0 1) (by simp) with h25207 | h25207
                · linarith only [h0, h25207, hlam]
                · rcases p25089_3 (m.d 0 2) (by simp) with h25209 | h25209
                  · rcases p25089_3 (m.d 0 3) (by simp) with h25210 | h25210
                    · linarith only [h20408, h25210, hlam]
                    · rcases p25089_3 (m.d 0 4) (by simp) with h25212 | h25212
                      · linarith only [h20409, h25212, hlam]
                      · linarith only [h25076, h25212, hlam]
                  · linarith only [h20410, h25209, hlam]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [h20411, h25077, h25080, hc01, hc12, hlam, hphi, p25089_1]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [h20408, hlam, p25089_1]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [hlam, p25089_0]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [h20411, hlam, p25089_1]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [h24656, hlam, p25089_1]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [h20411, h25077, h25080, hc01, hc12, hlam, hphi, p25089_1]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [h20409, hlam, p25089_0]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [h14396, h20411, h25077, h25080, hc01, hc12, hlam, hphi, p25089_1]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [hlam, p25089_0]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [h18815, h20411, h25077, h25080, hc01, hc12, hlam, hphi, p25089_1]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [h24656, h25077, h25080, h25088, hc01, hc12, hlam, hphi, p25089_1]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [h20410, hlam, p25089_1]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [h14396, h24656, h25077, h25080, h25088, hc01, hc12, hlam, hphi, p25089_1]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [h25076, hlam, p25089_1]
              · have p25089_0 := h25089c.1
                have p25089_1 := h25089c.2.1
                have p25089_2 := h25089c.2.2.1
                have p25089_3 := h25089c.2.2.2
                linarith only [hlam, p25089_0]
            · linarith only [h20411, h25076, h25088, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h25232 | h25232
            · rcases h0bigk with h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c | h25233c
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [hlam, p25233_0]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [h0, hlam, p25233_1]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [h14396, hlam, p25233_0]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [h16915, hlam, p25233_1]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [h18815, hlam, p25233_1]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                rcases p25233_3 (m.d 0 1) (by simp) with h25239 | h25239
                · linarith only [h0, h25239, hlam]
                · rcases p25233_3 (m.d 0 2) (by simp) with h25241 | h25241
                  · rcases p25233_3 (m.d 0 3) (by simp) with h25242 | h25242
                    · linarith only [h20408, h25242, hlam]
                    · linarith only [h14396, h25242, hlam]
                  · linarith only [h0, h25241, hlam]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [hlam, p25233_0]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                rcases p25233_3 (m.d 0 1) (by simp) with h25247 | h25247
                · linarith only [h0, h25247, hlam]
                · rcases p25233_3 (m.d 0 2) (by simp) with h25249 | h25249
                  · rcases p25233_3 (m.d 0 3) (by simp) with h25250 | h25250
                    · linarith only [h20408, h25250, hlam]
                    · rcases p25233_3 (m.d 0 4) (by simp) with h25252 | h25252
                      · linarith only [h20409, h25252, hlam]
                      · linarith only [h20411, h25252, hlam]
                  · linarith only [h20408, h25249, hlam]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [h0, h25076, h25083, h25087, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25233_1]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                rcases p25233_3 (m.d 0 1) (by simp) with h25257 | h25257
                · linarith only [h0, h25257, hlam]
                · rcases p25233_3 (m.d 0 2) (by simp) with h25259 | h25259
                  · rcases p25233_3 (m.d 0 3) (by simp) with h25260 | h25260
                    · linarith only [h20408, h25260, hlam]
                    · rcases p25233_3 (m.d 0 4) (by simp) with h25262 | h25262
                      · linarith only [h20409, h25262, hlam]
                      · linarith only [h25076, h25262, hlam]
                  · linarith only [h20410, h25259, hlam]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [h20411, hc01, hc34, hlam, hphi, ht12, ht23, p25233_1]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [h20408, hlam, p25233_1]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [hlam, p25233_0]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [h20411, hlam, p25233_1]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [h24656, hlam, p25233_1]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [h20411, h25077, h25080, hc01, hc12, hlam, hphi, p25233_1]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [h20409, hlam, p25233_0]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [h14396, h20411, h25077, h25080, hc01, hc12, hlam, hphi, p25233_1]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [hlam, p25233_0]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [h20411, h25076, h25077, h25080, h25083, h25087, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25233_1]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [h24656, h25077, h25080, h25232, hc01, hc12, hlam, hphi, p25233_1]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [h20410, hlam, p25233_1]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [h14396, h24656, h25077, h25080, h25232, hc01, hc12, hlam, hphi, p25233_1]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [h25076, hlam, p25233_1]
              · have p25233_0 := h25233c.1
                have p25233_1 := h25233c.2.1
                have p25233_2 := h25233c.2.2.1
                have p25233_3 := h25233c.2.2.2
                linarith only [hlam, p25233_0]
            · linarith only [h20411, h25076, h25232, hlam]
    · linarith only [h16915, h20411, h25076, h25077, h25080, h25082, hc01, hc12, hlam, hphi]
  · linarith only [h14396, h20411, h25080, h25081, hc01, hc35, hlam, hphi, ht12, ht23]

end R2N4
