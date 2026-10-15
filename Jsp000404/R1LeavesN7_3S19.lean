import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h12604 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 0 4 5 (by decide) (by decide) with h12605 | h12605
  · rcases m.htr 1 2 3 (by decide) (by decide) with h12606 | h12606
    · linarith only [h0, h12606, h4, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h12608 | h12608
      · linarith only [h0, h12608, h8674, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h12610 | h12610
        · linarith only [h0, h12610, h9870, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h12612 | h12612
          · linarith only [h1, h10361, h12604, h12612, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h12614 | h12614
            · rcases m.htr 1 4 5 (by decide) (by decide) with h12615 | h12615
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12616 | h12616
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12617 | h12617
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12618 | h12618
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12619 | h12619
                      · rcases h1bigk with h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c | h12620c
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [hlam, p12620_0]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          rcases p12620_3 (m.d 0 1) (by simp) with h12622 | h12622
                          · rcases p12620_3 (m.d 1 2) (by simp) with h12623 | h12623
                            · linarith only [h12623, hlam, p12620_0]
                            · rcases p12620_3 (m.d 1 3) (by simp) with h12625 | h12625
                              · linarith only [h1, h12625, hlam]
                              · linarith only [h12606, h12625, hlam]
                          · linarith only [h12622, hlam, p12620_0]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          rcases p12620_3 (m.d 0 1) (by simp) with h12629 | h12629
                          · rcases p12620_3 (m.d 1 2) (by simp) with h12630 | h12630
                            · linarith only [h0, h12630, hlam]
                            · rcases p12620_3 (m.d 1 3) (by simp) with h12632 | h12632
                              · linarith only [h12632, hlam, p12620_0]
                              · rcases p12620_3 (m.d 1 4) (by simp) with h12634 | h12634
                                · linarith only [h12634, h2, hlam]
                                · linarith only [h12612, h12634, hlam]
                          · linarith only [h12629, hlam, p12620_0]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          rcases p12620_3 (m.d 0 1) (by simp) with h12638 | h12638
                          · rcases p12620_3 (m.d 1 2) (by simp) with h12639 | h12639
                            · linarith only [h0, h12639, hlam]
                            · rcases p12620_3 (m.d 1 3) (by simp) with h12641 | h12641
                              · linarith only [h1, h12641, hlam]
                              · rcases p12620_3 (m.d 1 4) (by simp) with h12643 | h12643
                                · linarith only [h12643, hlam, p12620_0]
                                · rcases p12620_3 (m.d 1 5) (by simp) with h12645 | h12645
                                  · linarith only [h12645, h3, hlam]
                                  · rcases h3bigk with h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c | h12647c
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [hlam, p12647_0]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [h10361, h12614, h12619, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p12647_1]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [h4, hlam, p12647_1]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [h10361, hlam, p12647_0]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [h10361, h12616, h12619, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p12647_1]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [h1, hlam, p12647_0]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [hlam, p12647_0]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [h12606, hlam, p12647_1]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [h12612, hlam, p12647_0]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [h1, h10361, h12616, h12619, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p12647_1]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      rcases p12647_3 (m.d 0 3) (by simp) with h12658 | h12658
                                      · linarith only [h12658, h4, hlam]
                                      · rcases p12647_3 (m.d 1 3) (by simp) with h12660 | h12660
                                        · linarith only [h12606, h12660, hlam]
                                        · rcases p12647_3 (m.d 2 3) (by simp) with h12662 | h12662
                                          · rcases p12647_3 (m.d 3 4) (by simp) with h12663 | h12663
                                            · linarith only [h12616, h12663, hlam]
                                            · linarith only [h10361, h12663, hlam]
                                          · linarith only [h12662, h4, hlam]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      rcases p12647_3 (m.d 0 3) (by simp) with h12667 | h12667
                                      · linarith only [h12667, h4, hlam]
                                      · linarith only [h1, h12667, hlam]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [hlam, p12647_0]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [h10361, h12604, h9870, hc02, hc23, hlam, hphi, p12647_1]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [h1, h10361, h12614, h12616, hlam, p12647_2]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [h1, h12614, h12616, h12619, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p12647_1]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [h12614, h12616, h12619, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p12647_1]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [h12616, hlam, p12647_0]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [hlam, p12647_0]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      rcases p12647_3 (m.d 0 3) (by simp) with h12677 | h12677
                                      · linarith only [h10361, h12677, hlam]
                                      · linarith only [h12604, h12677, hlam]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [h12604, hlam, p12647_0]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [h12614, hlam, p12647_0]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [h12617, hlam, p12647_0]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [h12619, hlam, p12647_0]
                                    · have p12647_0 := h12647c.1
                                      have p12647_1 := h12647c.2.1
                                      have p12647_2 := h12647c.2.2.1
                                      have p12647_3 := h12647c.2.2.2
                                      linarith only [hlam, p12647_0]
                          · linarith only [h12638, hlam, p12620_0]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          rcases p12620_3 (m.d 0 1) (by simp) with h12686 | h12686
                          · rcases p12620_3 (m.d 1 2) (by simp) with h12687 | h12687
                            · linarith only [h0, h12687, hlam]
                            · rcases p12620_3 (m.d 1 3) (by simp) with h12689 | h12689
                              · linarith only [h1, h12689, hlam]
                              · linarith only [h12614, h12689, hlam]
                          · linarith only [h12686, hlam, p12620_0]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [h0, hlam, p12620_0]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [hlam, p12620_0]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [h12606, hlam, p12620_0]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [h12608, hlam, p12620_0]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [h12610, hlam, p12620_0]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [h1, hlam, p12620_0]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [h1, h10361, h12616, hc12, hc23, hlam, hphi, p12620_1]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [hlam, p12620_0]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [h12612, hlam, p12620_1]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [h1, h10361, h12616, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p12620_1]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [h2, hlam, p12620_0]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [h10361, h12616, h2, hc12, hc23, hlam, hphi, p12620_1]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [h10361, h12606, h12616, h2, hc12, hc23, hlam, hphi, p12620_1]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [hlam, p12620_0]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [h10361, h12610, h12616, h2, hc12, hc23, hlam, hphi, p12620_1]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [h3, hlam, p12620_0]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [h10361, h12604, h12616, h3, hc12, hc23, hlam, hphi, p12620_1]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [h12614, hlam, p12620_0]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [h12615, hlam, p12620_0]
                        · have p12620_0 := h12620c.1
                          have p12620_1 := h12620c.2.1
                          have p12620_2 := h12620c.2.2.1
                          have p12620_3 := h12620c.2.2.2
                          linarith only [hlam, p12620_0]
                      · linarith only [h10361, h12605, h12619, hlam]
                    · linarith only [h0, h10361, h12604, h12615, h12618, h3, h8674, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h10361, h12616, h12617, hc03, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12716 | h12716
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12717 | h12717
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12718 | h12718
                      · rcases h1bigk with h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c | h12719c
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [hlam, p12719_0]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          rcases p12719_3 (m.d 0 1) (by simp) with h12721 | h12721
                          · rcases p12719_3 (m.d 1 2) (by simp) with h12722 | h12722
                            · linarith only [h12722, hlam, p12719_0]
                            · rcases p12719_3 (m.d 1 3) (by simp) with h12724 | h12724
                              · linarith only [h1, h12724, hlam]
                              · linarith only [h12606, h12724, hlam]
                          · linarith only [h12721, hlam, p12719_0]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          rcases p12719_3 (m.d 0 1) (by simp) with h12728 | h12728
                          · rcases p12719_3 (m.d 1 2) (by simp) with h12729 | h12729
                            · linarith only [h0, h12729, hlam]
                            · rcases p12719_3 (m.d 1 3) (by simp) with h12731 | h12731
                              · linarith only [h12731, hlam, p12719_0]
                              · rcases p12719_3 (m.d 1 4) (by simp) with h12733 | h12733
                                · linarith only [h12733, h2, hlam]
                                · linarith only [h12612, h12733, hlam]
                          · linarith only [h12728, hlam, p12719_0]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          rcases p12719_3 (m.d 0 1) (by simp) with h12737 | h12737
                          · rcases p12719_3 (m.d 1 2) (by simp) with h12738 | h12738
                            · linarith only [h0, h12738, hlam]
                            · rcases p12719_3 (m.d 1 3) (by simp) with h12740 | h12740
                              · linarith only [h1, h12740, hlam]
                              · rcases p12719_3 (m.d 1 4) (by simp) with h12742 | h12742
                                · linarith only [h12742, hlam, p12719_0]
                                · rcases p12719_3 (m.d 1 5) (by simp) with h12744 | h12744
                                  · linarith only [h12744, h3, hlam]
                                  · rcases h3bigk with h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c | h12746c
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [hlam, p12746_0]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [h12616, h4, hc13, hc34, hlam, hphi, p12746_1]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [h4, hlam, p12746_1]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [h10361, hlam, p12746_0]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      rcases p12746_3 (m.d 0 3) (by simp) with h12751 | h12751
                                      · rcases p12746_3 (m.d 1 3) (by simp) with h12752 | h12752
                                        · linarith only [h1, h12752, hlam]
                                        · linarith only [h12614, h12752, hlam]
                                      · linarith only [h12751, hlam, p12746_0]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [h1, hlam, p12746_0]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [hlam, p12746_0]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [h12606, hlam, p12746_1]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [h12612, hlam, p12746_0]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [h12612, h12718, hc01, hc45, hlam, hphi, ht0b, ht5b, p12719_1, p12746_1]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [h12616, hc03, hc34, hlam, hphi, p12746_1]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [h12616, hc13, hc34, hlam, hphi, p12746_1]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [hlam, p12746_0]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [h12616, hlam, p12746_0]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      rcases p12746_3 (m.d 0 3) (by simp) with h12765 | h12765
                                      · linarith only [h12765, h4, hlam]
                                      · linarith only [h12604, h12765, hlam]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      rcases p12746_3 (m.d 0 3) (by simp) with h12768 | h12768
                                      · linarith only [h12768, hlam, p12746_0]
                                      · rcases p12746_3 (m.d 1 3) (by simp) with h12770 | h12770
                                        · linarith only [h12612, h12770, hlam]
                                        · rcases p12746_3 (m.d 2 3) (by simp) with h12772 | h12772
                                          · linarith only [h12616, h12772, hlam]
                                          · linarith only [h12772, h4, hlam]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      rcases p12746_3 (m.d 0 3) (by simp) with h12775 | h12775
                                      · linarith only [h10361, h12775, hlam]
                                      · linarith only [h1, h12775, hlam]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p12746_1]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [hlam, p12746_0]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      rcases p12746_3 (m.d 0 3) (by simp) with h12780 | h12780
                                      · linarith only [h10361, h12780, hlam]
                                      · linarith only [h12604, h12780, hlam]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [h12604, hlam, p12746_0]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [h12614, hlam, p12746_0]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [h12716, hlam, p12746_0]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [h12718, hlam, p12746_0]
                                    · have p12746_0 := h12746c.1
                                      have p12746_1 := h12746c.2.1
                                      have p12746_2 := h12746c.2.2.1
                                      have p12746_3 := h12746c.2.2.2
                                      linarith only [hlam, p12746_0]
                          · linarith only [h12737, hlam, p12719_0]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          rcases p12719_3 (m.d 0 1) (by simp) with h12789 | h12789
                          · rcases p12719_3 (m.d 1 2) (by simp) with h12790 | h12790
                            · linarith only [h0, h12790, hlam]
                            · rcases p12719_3 (m.d 1 3) (by simp) with h12792 | h12792
                              · linarith only [h1, h12792, hlam]
                              · linarith only [h12614, h12792, hlam]
                          · linarith only [h12789, hlam, p12719_0]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [h0, hlam, p12719_0]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [hlam, p12719_0]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [h12606, hlam, p12719_0]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [h12608, hlam, p12719_0]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [h12610, hlam, p12719_0]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [h1, hlam, p12719_0]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [h1, h10361, hc12, hc34, hlam, hphi, ht23, p12719_1]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [hlam, p12719_0]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [h12612, hlam, p12719_1]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [h1, h10361, h12610, hc12, hc34, hlam, hphi, ht23, p12719_1]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [h2, hlam, p12719_0]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          rcases p12719_3 (m.d 0 1) (by simp) with h12807 | h12807
                          · rcases p12719_3 (m.d 1 2) (by simp) with h12808 | h12808
                            · linarith only [h12608, h12808, hlam]
                            · rcases p12719_3 (m.d 1 3) (by simp) with h12810 | h12810
                              · linarith only [h12612, h12810, hlam]
                              · linarith only [h12606, h12810, hlam]
                          · linarith only [h0, h12807, hlam]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [h12614, h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p12719_1]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [hlam, p12719_0]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          rcases p12719_3 (m.d 0 1) (by simp) with h12816 | h12816
                          · rcases p12719_3 (m.d 1 2) (by simp) with h12817 | h12817
                            · linarith only [h12608, h12817, hlam]
                            · rcases p12719_3 (m.d 1 3) (by simp) with h12819 | h12819
                              · linarith only [h12612, h12819, hlam]
                              · linarith only [h12614, h12819, hlam]
                          · linarith only [h12816, h3, hlam]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [h3, hlam, p12719_0]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [h12604, h12616, h3, h4, hc12, hc34, hlam, hphi, ht23, p12719_1]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [h12614, hlam, p12719_0]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [h12615, hlam, p12719_0]
                        · have p12719_0 := h12719c.1
                          have p12719_1 := h12719c.2.1
                          have p12719_2 := h12719c.2.2.1
                          have p12719_3 := h12719c.2.2.2
                          linarith only [hlam, p12719_0]
                      · linarith only [h0, h12616, h12718, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h0, h1, h12614, h12615, h12616, h12717, h4, h8674, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h12604, h12716, h4, hlam]
              · linarith only [h12612, h12614, h12615, hlam]
            · linarith only [h10361, h12604, h12614, hc13, hc34, hlam, hphi]
  · linarith only [h10361, h12604, h12605, hlam]

end R2N4
