import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S82
import Jsp000404.R1LeavesN7_0S84

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 0 2 4 (by decide) (by decide) with h40600 | h40600
  · rcases m.htr 0 2 5 (by decide) (by decide) with h40601 | h40601
    · rcases m.htr 0 3 4 (by decide) (by decide) with h40602 | h40602
      · rcases m.htr 0 3 5 (by decide) (by decide) with h40603 | h40603
        · rcases m.htr 0 4 5 (by decide) (by decide) with h40604 | h40604
          · rcases m.htr 1 2 3 (by decide) (by decide) with h40605 | h40605
            · rcases m.htr 1 2 4 (by decide) (by decide) with h40606 | h40606
              · rcases m.htr 1 2 5 (by decide) (by decide) with h40607 | h40607
                · rcases m.htr 1 3 4 (by decide) (by decide) with h40608 | h40608
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h40609 | h40609
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h40610 | h40610
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h40611 | h40611
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h40612 | h40612
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h40613 | h40613
                            · linarith only [h39228, h40600, h40605, h40613, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h39228, h40600, h40604, h40605, h40613, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h39227, h39228, h40603, h40607, h40612, hc03, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h39228, h40602, h40611, hlam]
                      · linarith only [h36828, h39227, h40600, h40604, h40610, hc02, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h33187, h40603, h40609, hlam]
                  · linarith only [h39228, h40600, h40602, h40605, h40608, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h36828, h39227, h39228, h40600, h40605, h40607, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h39228, h40600, h40605, h40606, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h40623 | h40623
              · rcases m.htr 1 2 5 (by decide) (by decide) with h40624 | h40624
                · rcases m.htr 1 3 4 (by decide) (by decide) with h40625 | h40625
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h40626 | h40626
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h40627 | h40627
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h40628 | h40628
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h40629 | h40629
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h40630 | h40630
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h40631 | h40631
                              · rcases h1bigk with h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c | h40632c
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [hlam, p40632_0]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [h0, hlam, p40632_0]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [h33187, hlam, p40632_0]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [h36828, hlam, p40632_0]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [h36828, h40605, h40623, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p40632_1]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [h40605, hc01, hc23, hlam, hphi, ht12, p40632_1]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [hlam, p40632_0]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [h40605, hlam, p40632_1]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [h36828, h40605, hc01, hc23, hlam, hphi, ht12, p40632_1]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  rcases p40632_3 (m.d 0 1) (by simp) with h40642 | h40642
                                  · linarith only [h0, h40642, hlam]
                                  · linarith only [h39227, h40642, hlam]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  rcases p40632_3 (m.d 0 1) (by simp) with h40645 | h40645
                                  · linarith only [h40645, hlam, p40632_0]
                                  · rcases p40632_3 (m.d 1 2) (by simp) with h40647 | h40647
                                    · linarith only [h40605, h40647, hlam]
                                    · linarith only [h0, h40647, hlam]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [h0, h39227, h40605, h40624, h40629, h40631, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40632_1]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [hlam, p40632_0]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [h36828, h39227, h40605, h40624, h40629, h40631, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40632_1]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  rcases p40632_3 (m.d 0 1) (by simp) with h40653 | h40653
                                  · linarith only [h33187, h40653, hlam]
                                  · linarith only [h39227, h40653, hlam]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [h39227, h40605, h40623, h40624, h40629, h40631, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40632_1]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [h40623, hlam, p40632_0]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [h40625, hlam, p40632_1]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [hlam, p40632_0]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  rcases p40632_3 (m.d 0 1) (by simp) with h40660 | h40660
                                  · linarith only [h36828, h40660, hlam]
                                  · linarith only [h39227, h40660, hlam]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [h39227, hlam, p40632_0]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [h40624, hlam, p40632_0]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [h40626, hlam, p40632_0]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [h40627, hlam, p40632_0]
                                · have p40632_0 := h40632c.1
                                  have p40632_1 := h40632c.2.1
                                  have p40632_2 := h40632c.2.2.1
                                  have p40632_3 := h40632c.2.2.2
                                  linarith only [hlam, p40632_0]
                              · linarith only [h0, h39227, h40605, h40627, h40631, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h36828, h39227, h40605, h40623, h40627, h40630, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h36828, h40605, h40623, h40629, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h36828, h39227, h40605, h40623, h40627, h40628, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h36828, h40604, h40627, hlam]
                    · linarith only [h33187, h40603, h40626, hlam]
                  · linarith only [h0, h33187, h40600, h40602, h40605, h40625, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h40601, h40624, hlam]
              · linarith only [h0, h40600, h40623, hlam]
          · linarith only [h36828, h39227, h40604, hlam]
        · linarith only [h0, h39227, h39228, h40603, hlam]
      · linarith only [h39228, h40600, h40602, hlam]
    · linarith only [h36828, h39227, h40600, h40601, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h40681 | h40681
    · rcases m.htr 0 3 4 (by decide) (by decide) with h40682 | h40682
      · rcases m.htr 0 3 5 (by decide) (by decide) with h40683 | h40683
        · rcases m.htr 0 4 5 (by decide) (by decide) with h40684 | h40684
          · rcases m.htr 1 2 3 (by decide) (by decide) with h40685 | h40685
            · rcases m.htr 1 2 4 (by decide) (by decide) with h40686 | h40686
              · rcases m.htr 1 2 5 (by decide) (by decide) with h40687 | h40687
                · rcases m.htr 1 3 4 (by decide) (by decide) with h40688 | h40688
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h40689 | h40689
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h40690 | h40690
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h40691 | h40691
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h40692 | h40692
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h40693 | h40693
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h40694 | h40694
                              · rcases h1bigk with h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c | h40695c
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [hlam, p40695_0]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [h0, hlam, p40695_0]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [h33187, hlam, p40695_0]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [h36828, hlam, p40695_0]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [h0, h40600, h40685, h40687, h40691, h40692, h40694, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40695_1]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  rcases p40695_3 (m.d 0 1) (by simp) with h40701 | h40701
                                  · linarith only [h40701, hlam, p40695_0]
                                  · rcases p40695_3 (m.d 1 2) (by simp) with h40703 | h40703
                                    · rcases p40695_3 (m.d 1 3) (by simp) with h40704 | h40704
                                      · linarith only [h40685, h40704, hlam]
                                      · linarith only [h33187, h40704, hlam]
                                    · linarith only [h40703, hlam, p40695_0]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [hlam, p40695_0]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [h0, h40600, h40686, h40688, hc01, hc12, hlam, hphi, p40695_1]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [h0, h39227, h40600, h40686, h40687, h40692, h40694, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40695_1]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [h0, h39227, h39228, h40685, hlam, p40695_2]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  rcases p40695_3 (m.d 0 1) (by simp) with h40712 | h40712
                                  · linarith only [h40712, hlam, p40695_0]
                                  · rcases p40695_3 (m.d 1 2) (by simp) with h40714 | h40714
                                    · rcases p40695_3 (m.d 1 3) (by simp) with h40715 | h40715
                                      · rcases p40695_3 (m.d 1 4) (by simp) with h40716 | h40716
                                        · linarith only [h40688, h40716, hlam]
                                        · linarith only [h36828, h40716, hlam]
                                      · linarith only [h40715, hlam, p40695_0]
                                    · linarith only [h0, h40714, hlam]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [h40685, hlam, p40695_0]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [hlam, p40695_0]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [h0, h39227, h40600, h40686, h40687, h40692, h40694, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p40695_1]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  rcases p40695_3 (m.d 0 1) (by simp) with h40724 | h40724
                                  · linarith only [h33187, h40724, hlam]
                                  · linarith only [h39227, h40724, hlam]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  rcases p40695_3 (m.d 0 1) (by simp) with h40727 | h40727
                                  · linarith only [h40727, hlam, p40695_0]
                                  · rcases p40695_3 (m.d 1 2) (by simp) with h40729 | h40729
                                    · rcases p40695_3 (m.d 1 3) (by simp) with h40730 | h40730
                                      · rcases p40695_3 (m.d 1 4) (by simp) with h40731 | h40731
                                        · rcases p40695_3 (m.d 1 5) (by simp) with h40732 | h40732
                                          · linarith only [h40690, h40732, hlam]
                                          · rcases h1emax with h40734 | h40734 | h40734 | h40734 | h40734
                                            · rcases h2bigk with h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c | h40735c
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [hlam, p40735_0]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [h0, hlam, p40735_0]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [h39228, hlam, p40735_0]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [h40600, hlam, p40735_0]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [h40600, h40685, h40691, h40692, h40694, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40735_1]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                rcases p40735_3 (m.d 0 2) (by simp) with h40741 | h40741
                                                · linarith only [h0, h40741, hlam]
                                                · rcases p40735_3 (m.d 1 2) (by simp) with h40743 | h40743
                                                  · rcases p40735_3 (m.d 2 3) (by simp) with h40744 | h40744
                                                    · linarith only [h40685, h40744, hlam]
                                                    · linarith only [h39228, h40744, hlam]
                                                  · linarith only [h0, h40743, hlam]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [hlam, p40735_0]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [h0, h39227, h40600, h40687, h40691, h40692, h40694, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40735_1]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [h0, h39227, h40600, h40687, h40692, h40694, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40735_1]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [h0, h39227, h40600, h40685, h40687, h40691, hlam, p40735_2]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [h0, h39227, h40685, h40687, h40692, h40694, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40735_1]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [h40685, hlam, p40735_0]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [hlam, p40735_0]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [h0, h39227, h40600, h40685, h40687, h40692, h40694, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40735_1]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                rcases p40735_3 (m.d 0 2) (by simp) with h40756 | h40756
                                                · linarith only [h39228, h40756, hlam]
                                                · linarith only [h40681, h40756, hlam]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [h0, h39227, h40686, h40687, h40692, h40694, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40735_1]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [h40686, hlam, p40735_0]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [h40691, hlam, p40735_0]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [hlam, p40735_0]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                rcases p40735_3 (m.d 0 2) (by simp) with h40763 | h40763
                                                · linarith only [h40600, h40763, hlam]
                                                · linarith only [h40681, h40763, hlam]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [h40681, hlam, p40735_0]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [h40687, hlam, p40735_0]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [h40692, hlam, p40735_0]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [h40693, hlam, p40735_1]
                                              · have p40735_0 := h40735c.1
                                                have p40735_1 := h40735c.2.1
                                                have p40735_2 := h40735c.2.2.1
                                                have p40735_3 := h40735c.2.2.2
                                                linarith only [hlam, p40735_0]
                                            · linarith only [h0, h39227, h40687, h40692, h40694, h40734, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                            · linarith only [h39227, h40687, h40688, h40692, h40694, h40734, hc45, hlam, hphi, ht01, ht0b, ht5b, p40695_1]
                                            · linarith only [h39227, h40687, h40692, h40694, h40734, hc45, hlam, hphi, ht01, ht0b, ht5b, p40695_1]
                                            · rcases h2bigk with h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c | h40774c
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [hlam, p40774_0]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [h0, hlam, p40774_0]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [h39228, hlam, p40774_0]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [h40600, hlam, p40774_0]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [h40600, h40685, h40691, h40692, h40694, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40774_1]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                rcases p40774_3 (m.d 0 2) (by simp) with h40780 | h40780
                                                · linarith only [h0, h40780, hlam]
                                                · rcases p40774_3 (m.d 1 2) (by simp) with h40782 | h40782
                                                  · rcases p40774_3 (m.d 2 3) (by simp) with h40783 | h40783
                                                    · linarith only [h40685, h40783, hlam]
                                                    · linarith only [h39228, h40783, hlam]
                                                  · linarith only [h0, h40782, hlam]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [hlam, p40774_0]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [h0, h39227, h40600, h40687, h40691, h40692, h40694, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40774_1]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [h0, h39227, h40600, h40687, h40692, h40694, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40774_1]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [h0, h39227, h40600, h40685, h40687, h40691, hlam, p40774_2]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [h0, h39227, h40685, h40687, h40692, h40694, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40774_1]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [h40685, hlam, p40774_0]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [hlam, p40774_0]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [h0, h39227, h40600, h40685, h40687, h40692, h40694, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40774_1]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                rcases p40774_3 (m.d 0 2) (by simp) with h40795 | h40795
                                                · linarith only [h39228, h40795, hlam]
                                                · linarith only [h40681, h40795, hlam]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [h0, h39227, h40686, h40687, h40692, h40694, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40774_1]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [h40686, hlam, p40774_0]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [h40691, hlam, p40774_0]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [hlam, p40774_0]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                rcases p40774_3 (m.d 0 2) (by simp) with h40802 | h40802
                                                · linarith only [h40600, h40802, hlam]
                                                · linarith only [h40681, h40802, hlam]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [h40681, hlam, p40774_0]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [h40687, hlam, p40774_0]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [h40692, hlam, p40774_0]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [h40693, hlam, p40774_1]
                                              · have p40774_0 := h40774c.1
                                                have p40774_1 := h40774c.2.1
                                                have p40774_2 := h40774c.2.2.1
                                                have p40774_3 := h40774c.2.2.2
                                                linarith only [hlam, p40774_0]
                                        · linarith only [h40731, hlam, p40695_0]
                                      · linarith only [h33187, h40730, hlam]
                                    · linarith only [h0, h40729, hlam]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [h40686, hlam, p40695_0]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [h40688, hlam, p40695_1]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [hlam, p40695_0]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  rcases p40695_3 (m.d 0 1) (by simp) with h40816 | h40816
                                  · linarith only [h36828, h40816, hlam]
                                  · linarith only [h39227, h40816, hlam]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [h39227, hlam, p40695_0]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [h40687, hlam, p40695_0]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [h40689, hlam, p40695_0]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [h40690, hlam, p40695_0]
                                · have p40695_0 := h40695c.1
                                  have p40695_1 := h40695c.2.1
                                  have p40695_2 := h40695c.2.2.1
                                  have p40695_3 := h40695c.2.2.2
                                  linarith only [hlam, p40695_0]
                              · linarith only [h0, h39227, h39228, h40685, h40690, h40694, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h39227, h40600, h40690, h40693, hlam]
                          · linarith only [h0, h39227, h40600, h40683, h40691, h40692, hc03, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h39228, h40682, h40691, hlam]
                      · linarith only [h36828, h39227, h40684, h40690, hc04, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h33187, h39228, h40683, h40685, h40689, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h39227, h39228, h40682, h40685, h40687, h40688, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h39227, h39228, h40685, h40687, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h0, h39227, h39228, h40685, h40686, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h40833 | h40833
              · linarith only [h0, h39227, h40600, h40685, h40833, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h40835 | h40835
                · rcases m.htr 1 3 4 (by decide) (by decide) with h40836 | h40836
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h40837 | h40837
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h40838 | h40838
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h40839 | h40839
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h40840 | h40840
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h40841 | h40841
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h40842 | h40842
                              · rcases h1bigk with h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c | h40843c
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [hlam, p40843_0]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [h0, hlam, p40843_0]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [h33187, hlam, p40843_0]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [h36828, hlam, p40843_0]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [h0, h40833, h40835, h40839, h40840, h40842, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40843_1]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [h40833, h40839, hc01, hc23, hlam, hphi, ht12, p40843_1]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [hlam, p40843_0]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [h40685, hlam, p40843_1]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [h40833, hlam, p40843_1]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  rcases p40843_3 (m.d 0 1) (by simp) with h40853 | h40853
                                  · linarith only [h0, h40853, hlam]
                                  · linarith only [h39227, h40853, hlam]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  rcases p40843_3 (m.d 0 1) (by simp) with h40856 | h40856
                                  · linarith only [h40856, hlam, p40843_0]
                                  · rcases p40843_3 (m.d 1 2) (by simp) with h40858 | h40858
                                    · linarith only [h40685, h40858, hlam]
                                    · linarith only [h0, h40858, hlam]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [h0, h39227, h40685, h40835, h40840, h40842, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40843_1]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [hlam, p40843_0]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [h36828, h39227, h40685, h40835, h40840, h40842, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40843_1]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  rcases p40843_3 (m.d 0 1) (by simp) with h40864 | h40864
                                  · linarith only [h33187, h40864, hlam]
                                  · linarith only [h39227, h40864, hlam]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  rcases p40843_3 (m.d 0 1) (by simp) with h40867 | h40867
                                  · linarith only [h40867, hlam, p40843_0]
                                  · rcases p40843_3 (m.d 1 2) (by simp) with h40869 | h40869
                                    · linarith only [h40833, h40869, hlam]
                                    · linarith only [h0, h40869, hlam]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [h0, h40833, h40839, hc01, hc23, hlam, hphi, ht12, p40843_1]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [h40836, hlam, p40843_1]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [hlam, p40843_0]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  rcases p40843_3 (m.d 0 1) (by simp) with h40875 | h40875
                                  · linarith only [h36828, h40875, hlam]
                                  · linarith only [h39227, h40875, hlam]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [h39227, hlam, p40843_0]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [h40835, hlam, p40843_0]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [h40837, hlam, p40843_0]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [h40838, hlam, p40843_0]
                                · have p40843_0 := h40843c.1
                                  have p40843_1 := h40843c.2.1
                                  have p40843_2 := h40843c.2.2.1
                                  have p40843_3 := h40843c.2.2.2
                                  linarith only [hlam, p40843_0]
                              · linarith only [h0, h39227, h40833, h40838, h40839, h40842, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h39227, h40833, h40838, h40841, hlam]
                          · linarith only [h0, h40833, h40839, h40840, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h33187, h40682, h40685, h40839, hlam]
                      · linarith only [h33187, h36828, h39227, h40682, h40684, h40835, h40838, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h33187, h40683, h40837, hlam]
                  · linarith only [h33187, h40682, h40836, hlam]
                · linarith only [h0, h39227, h40681, h40835, hc02, hc15, hlam, hphi, ht0b, ht5b]
          · linarith only [h36828, h39227, h40684, hlam]
        · linarith only [h33187, h39227, h40683, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h40893 | h40893
        · rcases m.htr 0 4 5 (by decide) (by decide) with h40894 | h40894
          · rcases m.htr 1 2 3 (by decide) (by decide) with h40895 | h40895
            · rcases m.htr 1 2 4 (by decide) (by decide) with h40896 | h40896
              · rcases m.htr 1 2 5 (by decide) (by decide) with h40897 | h40897
                · rcases m.htr 1 3 4 (by decide) (by decide) with h40898 | h40898
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h40899 | h40899
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h40900 | h40900
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h40901 | h40901
                        · linarith only [h0, h39228, h40682, h40895, h40901, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h39227, h39228, h40897, h40898, h40901, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h36828, h39227, h40894, h40897, h40900, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h39227, h39228, h40682, h40897, h40898, h40899, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h40906 | h40906
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h40907 | h40907
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h40908 | h40908
                        · linarith only [h40895, h40898, h40908, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h40910 | h40910
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h40911 | h40911
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h40912 | h40912
                              · rcases h1bigk with h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c | h40913c
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [hlam, p40913_0]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [h0, hlam, p40913_0]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [h33187, hlam, p40913_0]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [h36828, hlam, p40913_0]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [h0, h39228, h40895, h40897, h40898, h40910, h40912, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p40913_1]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  rcases p40913_3 (m.d 0 1) (by simp) with h40919 | h40919
                                  · linarith only [h40919, hlam, p40913_0]
                                  · rcases p40913_3 (m.d 1 2) (by simp) with h40921 | h40921
                                    · rcases p40913_3 (m.d 1 3) (by simp) with h40922 | h40922
                                      · linarith only [h40895, h40922, hlam]
                                      · linarith only [h33187, h40922, hlam]
                                    · linarith only [h40921, hlam, p40913_0]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [hlam, p40913_0]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [h0, h39228, h40895, hc01, hc12, hlam, hphi, p40913_1]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [h0, h39227, h39228, h40895, h40897, h40898, h40910, h40912, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40913_1]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [h0, h39227, h39228, h40895, hlam, p40913_2]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [h39227, h40897, h40898, h40910, h40912, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p40913_1]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [h40895, hlam, p40913_0]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [hlam, p40913_0]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [h40898, hlam, p40913_0]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  rcases p40913_3 (m.d 0 1) (by simp) with h40934 | h40934
                                  · linarith only [h33187, h40934, hlam]
                                  · linarith only [h39227, h40934, hlam]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  rcases p40913_3 (m.d 0 1) (by simp) with h40937 | h40937
                                  · linarith only [h40937, hlam, p40913_0]
                                  · rcases p40913_3 (m.d 1 2) (by simp) with h40939 | h40939
                                    · rcases p40913_3 (m.d 1 3) (by simp) with h40940 | h40940
                                      · linarith only [h40898, h40940, hlam]
                                      · linarith only [h33187, h40940, hlam]
                                    · linarith only [h0, h40939, hlam]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [h40896, hlam, p40913_0]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [h33187, h39227, h40897, h40910, h40912, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p40913_1]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [hlam, p40913_0]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  rcases p40913_3 (m.d 0 1) (by simp) with h40947 | h40947
                                  · linarith only [h36828, h40947, hlam]
                                  · linarith only [h39227, h40947, hlam]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [h39227, hlam, p40913_0]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [h40897, hlam, p40913_0]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [h40906, hlam, p40913_0]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [h40907, hlam, p40913_0]
                                · have p40913_0 := h40913c.1
                                  have p40913_1 := h40913c.2.1
                                  have p40913_2 := h40913c.2.2.1
                                  have p40913_3 := h40913c.2.2.2
                                  linarith only [hlam, p40913_0]
                              · linarith only [h0, h39227, h39228, h40682, h40894, h40897, h40910, h40912, hc04, hc35, hlam, hphi, ht0b, ht5b]
                            · linarith only [h36828, h39227, h40600, h40907, h40911, hlam]
                          · linarith only [h0, h39227, h39228, h40682, h40893, h40910, hc04, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h36828, h39227, h40894, h40897, h40907, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h39227, h39228, h40893, h40895, h40897, h40906, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h39227, h40600, h40896, h40897, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h0, h39227, h39228, h40895, h40896, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h40962 | h40962
              · linarith only [h0, h39227, h40600, h40895, h40962, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h40964 | h40964
                · rcases m.htr 1 3 4 (by decide) (by decide) with h40965 | h40965
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h40966 | h40966
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h40967 | h40967
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h40968 | h40968
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h40969 | h40969
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h40970 | h40970
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h40971 | h40971
                              · rcases h1bigk with h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c | h40972c
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [hlam, p40972_0]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [h0, hlam, p40972_0]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [h33187, hlam, p40972_0]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [h36828, hlam, p40972_0]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [h0, h40962, h40964, h40968, h40969, h40971, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40972_1]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [h40962, h40968, hc01, hc23, hlam, hphi, ht12, p40972_1]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [hlam, p40972_0]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [h40895, hlam, p40972_1]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [h40962, hlam, p40972_1]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  rcases p40972_3 (m.d 0 1) (by simp) with h40982 | h40982
                                  · linarith only [h0, h40982, hlam]
                                  · linarith only [h39227, h40982, hlam]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  rcases p40972_3 (m.d 0 1) (by simp) with h40985 | h40985
                                  · linarith only [h40985, hlam, p40972_0]
                                  · rcases p40972_3 (m.d 1 2) (by simp) with h40987 | h40987
                                    · linarith only [h40895, h40987, hlam]
                                    · linarith only [h0, h40987, hlam]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [h0, h39227, h40895, h40964, h40969, h40971, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40972_1]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [hlam, p40972_0]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [h36828, h39227, h40895, h40964, h40969, h40971, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40972_1]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [h33187, h39227, h40682, h40965, hlam, p40972_2]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  rcases p40972_3 (m.d 0 1) (by simp) with h40994 | h40994
                                  · linarith only [h40994, hlam, p40972_0]
                                  · rcases p40972_3 (m.d 1 2) (by simp) with h40996 | h40996
                                    · linarith only [h40962, h40996, hlam]
                                    · linarith only [h0, h40996, hlam]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [h0, h39227, h40964, h40969, h40971, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p40972_1]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [h40965, hlam, p40972_1]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [hlam, p40972_0]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  rcases p40972_3 (m.d 0 1) (by simp) with h41002 | h41002
                                  · linarith only [h36828, h41002, hlam]
                                  · linarith only [h39227, h41002, hlam]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [h39227, hlam, p40972_0]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [h40964, hlam, p40972_0]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [h40966, hlam, p40972_0]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [h40967, hlam, p40972_0]
                                · have p40972_0 := h40972c.1
                                  have p40972_1 := h40972c.2.1
                                  have p40972_2 := h40972c.2.2.1
                                  have p40972_3 := h40972c.2.2.2
                                  linarith only [hlam, p40972_0]
                              · linarith only [h40682, h40894, h40971, hlam]
                            · linarith only [h0, h39227, h39228, h40682, h40965, h40967, h40970, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h39228, h40682, h40895, h40965, h40969, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h40895, h40965, h40968, hlam]
                      · linarith only [h36828, h40894, h40967, hlam]
                    · linarith only [h0, h39228, h40682, h40965, h40966, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h41016 | h41016
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h41017 | h41017
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h41018 | h41018
                        · linarith only [h0, h40895, h40965, h41018, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h39227, h40895, h40964, h41018, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h36828, h40894, h41017, hlam]
                    · linarith only [h33187, h40893, h41016, hlam]
                · linarith only [h0, h40681, h40964, hlam]
          · linarith only [h33187, h39227, h40682, h40894, hlam]
        · linarith only [h0, h39227, h39228, h40893, hlam]
    · linarith only [h0, h39227, h40681, hlam]

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 0 2 3 (by decide) (by decide) with h39228 | h39228
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s39 m hb1 hb2 hb4 hb5 h0 h33187 h36828 h39227

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 0 1 5 (by decide) (by decide) with h39227 | h39227
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227

end R2N4
