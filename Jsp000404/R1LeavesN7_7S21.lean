import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S20

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 0 2 5 (by decide) (by decide) with h14601 | h14601
  · rcases m.htr 0 3 4 (by decide) (by decide) with h14602 | h14602
    · linarith only [h12233, h12234, h14602, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h14604 | h14604
      · rcases m.htr 0 4 5 (by decide) (by decide) with h14605 | h14605
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14606 | h14606
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14607 | h14607
            · linarith only [h12233, h12234, h14604, h14607, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14609 | h14609
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14610 | h14610
                · linarith only [h14602, h14604, h14610, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14612 | h14612
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14613 | h14613
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14614 | h14614
                      · linarith only [h0, h12233, h14607, h14610, h14614, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14616 | h14616
                        · linarith only [h0, h12233, h14607, h14614, h14616, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · linarith only [h0, h12233, h14604, h14607, h14614, h14616, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h12233, h14604, h14605, h14607, h14613, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h10472, h14604, h14612, hlam]
              · linarith only [h0, h14601, h14609, hlam]
          · linarith only [h0, h12233, h14606, hlam]
        · linarith only [h12233, h12234, h14604, h14605, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h14624 | h14624
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14625 | h14625
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14626 | h14626
            · linarith only [h12234, h14601, h14626, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14628 | h14628
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14629 | h14629
                · linarith only [h10472, h14602, h14625, h14626, h14629, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14631 | h14631
                  · linarith only [h10472, h14604, h14625, h14626, h14631, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14633 | h14633
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14634 | h14634
                      · linarith only [h10472, h14629, h14634, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14636 | h14636
                        · linarith only [h10472, h12233, h14631, h14636, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14638 | h14638
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14639 | h14639
                            · rcases h1bigk with h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c | h14640c
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [hlam, p14640_0]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h0, hlam, p14640_0]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h10472, hlam, p14640_0]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h11379, hlam, p14640_0]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h12013, hlam, p14640_0]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h14626, h14634, hc01, hc34, hlam, hphi, ht12, ht23, p14640_1]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [hlam, p14640_0]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h10472, h14626, h14634, hc01, hc34, hlam, hphi, ht12, ht23, p14640_1]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h14626, hlam, p14640_0]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h14626, h14634, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14640_1, u5ehi1]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h14631, hc01, hc35, hlam, hphi, ht12, ht23, p14640_1]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h14625, hlam, p14640_1]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [hlam, p14640_0]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h14629, hlam, p14640_1]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h14631, hlam, p14640_1]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                rcases p14640_3 (m.d 0 1) (by simp) with h14656 | h14656
                                · linarith only [h14656, hlam, p14640_0]
                                · rcases p14640_3 (m.d 1 2) (by simp) with h14658 | h14658
                                  · linarith only [h14626, h14658, hlam]
                                  · linarith only [h0, h14658, hlam]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h0, h14601, h14626, h14634, h14636, hc23, hc34, hlam, hphi, p14640_1]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h10472, h14626, h14634, hc01, hc34, hlam, hphi, ht12, ht23, p14640_1]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [hlam, p14640_0]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h10472, h14626, h14631, h14634, hc01, hc34, hlam, hphi, ht12, ht23, p14640_1]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h14626, h14628, h14634, hc01, hc34, hlam, hphi, ht12, ht23, p14640_1]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h14628, hlam, p14640_1]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h10472, h14626, h14628, h14634, hc01, hc34, hlam, hphi, ht12, ht23, p14640_1]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [h14633, hlam, p14640_0]
                              · have p14640_0 := h14640c.1
                                have p14640_1 := h14640c.2.1
                                have p14640_2 := h14640c.2.2.1
                                have p14640_3 := h14640c.2.2.2
                                linarith only [hlam, p14640_0]
                            · linarith only [h14601, h14626, h14628, h14634, h14638, h14639, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                          · linarith only [h0, h14601, h14626, h14638, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                    · linarith only [h0, h11379, h14601, h14624, h14626, h14633, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h14601, h14628, hlam]
          · linarith only [h0, h12233, h14625, hlam]
        · linarith only [h12234, h14601, h14624, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h14676 | h14676
    · linarith only [h12233, h12234, h14676, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h14678 | h14678
      · linarith only [h12233, h14601, h14678, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h14680 | h14680
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14681 | h14681
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14682 | h14682
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14683 | h14683
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14684 | h14684
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14685 | h14685
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14686 | h14686
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14687 | h14687
                      · linarith only [h12233, h12234, h14676, h14682, h14687, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14689 | h14689
                        · linarith only [h10472, h12233, h12234, h14678, h14681, h14684, h14687, h14689, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14691 | h14691
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14692 | h14692
                            · rcases h1bigk with h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c | h14693c
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [hlam, p14693_0]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [h0, hlam, p14693_0]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [h10472, hlam, p14693_0]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [h11379, hlam, p14693_0]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [h12013, hlam, p14693_0]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                rcases p14693_3 (m.d 0 1) (by simp) with h14699 | h14699
                                · linarith only [h14699, hlam, p14693_0]
                                · rcases p14693_3 (m.d 1 2) (by simp) with h14701 | h14701
                                  · rcases p14693_3 (m.d 1 3) (by simp) with h14702 | h14702
                                    · linarith only [h14681, h14702, hlam]
                                    · linarith only [h10472, h14702, hlam]
                                  · linarith only [h14701, hlam, p14693_0]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [hlam, p14693_0]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [h12233, h14601, h14684, h14687, h14691, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14693_1]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [h12233, h14601, h14685, h14686, h14689, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14693_1]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [h12233, h14601, h14685, h14689, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14693_1]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                rcases p14693_3 (m.d 0 1) (by simp) with h14710 | h14710
                                · linarith only [h14710, hlam, p14693_0]
                                · rcases p14693_3 (m.d 1 2) (by simp) with h14712 | h14712
                                  · rcases p14693_3 (m.d 1 3) (by simp) with h14713 | h14713
                                    · rcases p14693_3 (m.d 1 4) (by simp) with h14714 | h14714
                                      · linarith only [h14684, h14714, hlam]
                                      · linarith only [h11379, h14714, hlam]
                                    · linarith only [h14713, hlam, p14693_0]
                                  · linarith only [h0, h14712, hlam]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [h14681, hlam, p14693_1]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [hlam, p14693_0]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [h12233, h14601, h14685, h14686, h14689, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14693_1]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [h12233, h14601, h14681, h14685, h14689, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14693_1]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                rcases p14693_3 (m.d 0 1) (by simp) with h14723 | h14723
                                · linarith only [h14723, hlam, p14693_0]
                                · rcases p14693_3 (m.d 1 2) (by simp) with h14725 | h14725
                                  · rcases p14693_3 (m.d 1 3) (by simp) with h14726 | h14726
                                    · rcases p14693_3 (m.d 1 4) (by simp) with h14727 | h14727
                                      · rcases p14693_3 (m.d 1 5) (by simp) with h14728 | h14728
                                        · linarith only [h14686, h14728, hlam]
                                        · linarith only [h12013, h14728, hlam]
                                      · linarith only [h14727, hlam, p14693_0]
                                    · linarith only [h10472, h14726, hlam]
                                  · linarith only [h0, h14725, hlam]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [h14682, hlam, p14693_1]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [h14684, hlam, p14693_0]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [hlam, p14693_0]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [h12233, h14601, h14685, h14689, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14693_1]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                rcases p14693_3 (m.d 0 1) (by simp) with h14738 | h14738
                                · linarith only [h14738, hlam, p14693_0]
                                · rcases p14693_3 (m.d 1 2) (by simp) with h14740 | h14740
                                  · rcases p14693_3 (m.d 1 3) (by simp) with h14741 | h14741
                                    · rcases p14693_3 (m.d 1 4) (by simp) with h14742 | h14742
                                      · rcases p14693_3 (m.d 1 5) (by simp) with h14743 | h14743
                                        · rcases h1emax with h14744 | h14744 | h14744 | h14744 | h14744
                                          · rcases h3bigk with h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c | h14745c
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [hlam, p14745_0]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [h10472, hlam, p14745_1]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [h12233, h14601, h14687, h14691, hc23, hc34, hlam, hphi, p14745_1]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [h14676, hlam, p14745_0]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [h14678, hlam, p14745_0]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              rcases p14745_3 (m.d 0 3) (by simp) with h14751 | h14751
                                              · linarith only [h10472, h14751, hlam]
                                              · rcases p14745_3 (m.d 1 3) (by simp) with h14753 | h14753
                                                · rcases p14745_3 (m.d 2 3) (by simp) with h14754 | h14754
                                                  · linarith only [h14681, h14754, hlam]
                                                  · rcases p14745_3 (m.d 3 4) (by simp) with h14756 | h14756
                                                    · linarith only [h14684, h14756, hlam]
                                                    · linarith only [h14676, h14756, hlam]
                                                · linarith only [h10472, h14753, hlam]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [hlam, p14745_0]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [h12233, h14601, h14684, h14687, h14691, hlam, p14745_2]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [h0, h14601, h14681, h14687, h14691, hc01, hc12, hlam, hphi, p14745_1]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [h10472, h14678, h14681, hc01, hc12, hlam, hphi, p14745_1]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [h12233, hlam, p14745_0]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [h14681, hlam, p14745_0]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [hlam, p14745_0]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [h14687, hlam, p14745_0]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [h14689, hlam, p14745_0]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [h10472, h14681, h14684, hc01, hc12, hlam, hphi, p14745_1]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [h14684, hlam, p14745_0]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              rcases p14745_3 (m.d 0 3) (by simp) with h14771 | h14771
                                              · linarith only [h14676, h14771, hlam]
                                              · linarith only [h12233, h14771, hlam]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [hlam, p14745_0]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [h12233, h14601, h14681, h14684, h14689, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14745_1]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [h10472, h14681, h14685, hc01, hc12, hlam, hphi, p14745_1]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [h14685, hlam, p14745_0]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              rcases p14745_3 (m.d 0 3) (by simp) with h14778 | h14778
                                              · linarith only [h14678, h14778, hlam]
                                              · linarith only [h12233, h14778, hlam]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [h14692, hlam, p14745_0]
                                            · have p14745_0 := h14745c.1
                                              have p14745_1 := h14745c.2.1
                                              have p14745_2 := h14745c.2.2.1
                                              have p14745_3 := h14745c.2.2.2
                                              linarith only [hlam, p14745_0]
                                          · linarith only [h14681, h14684, h14692, h14744, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                          · linarith only [h12233, h14601, h14684, h14687, h14691, h14744, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                          · linarith only [h14686, h14744, hc01, hlam, p14693_1]
                                          · linarith only [h14744, hc01, hlam, p14693_1]
                                        · linarith only [h14743, hlam, p14693_0]
                                      · linarith only [h11379, h14742, hlam]
                                    · linarith only [h10472, h14741, hlam]
                                  · linarith only [h0, h14740, hlam]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [h14683, hlam, p14693_1]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [h14685, hlam, p14693_0]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [h14686, hlam, p14693_0]
                              · have p14693_0 := h14693c.1
                                have p14693_1 := h14693c.2.1
                                have p14693_2 := h14693c.2.2.1
                                have p14693_3 := h14693c.2.2.2
                                linarith only [hlam, p14693_0]
                            · linarith only [h12233, h14601, h14680, h14687, h14691, h14692, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · linarith only [h12234, h14680, h14691, hlam]
                    · linarith only [h11379, h12234, h14680, h14686, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h12233, h12234, h14676, h14684, h14685, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14799 | h14799
                  · linarith only [h10472, h14678, h14684, h14799, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14801 | h14801
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14802 | h14802
                      · linarith only [h12233, h14601, h14683, h14684, h14801, h14802, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14804 | h14804
                        · linarith only [h10472, h12233, h14799, h14804, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14806 | h14806
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14807 | h14807
                            · rcases h1bigk with h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c | h14808c
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [hlam, p14808_0]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [h0, hlam, p14808_0]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [h10472, hlam, p14808_0]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [h11379, hlam, p14808_0]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [h12013, hlam, p14808_0]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                rcases p14808_3 (m.d 0 1) (by simp) with h14814 | h14814
                                · linarith only [h14814, hlam, p14808_0]
                                · rcases p14808_3 (m.d 1 2) (by simp) with h14816 | h14816
                                  · rcases p14808_3 (m.d 1 3) (by simp) with h14817 | h14817
                                    · linarith only [h14681, h14817, hlam]
                                    · linarith only [h10472, h14817, hlam]
                                  · linarith only [h14816, hlam, p14808_0]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [hlam, p14808_0]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [h10472, hc01, hc12, hlam, hphi, p14808_1]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [h11379, hc01, hc12, hlam, hphi, p14808_1]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [h12013, hc01, hc12, hlam, hphi, p14808_1]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [h14684, hc01, hc34, hlam, hphi, ht12, ht23, p14808_1]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [h14681, hlam, p14808_1]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [hlam, p14808_0]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [h14684, hlam, p14808_1]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [h14799, hlam, p14808_1]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                rcases p14808_3 (m.d 0 1) (by simp) with h14830 | h14830
                                · linarith only [h14830, hlam, p14808_0]
                                · rcases p14808_3 (m.d 1 2) (by simp) with h14832 | h14832
                                  · rcases p14808_3 (m.d 1 3) (by simp) with h14833 | h14833
                                    · linarith only [h14684, h14833, hlam]
                                    · linarith only [h10472, h14833, hlam]
                                  · linarith only [h0, h14832, hlam]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [h14682, hlam, p14808_1]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [h10472, hc01, hc14, hlam, hphi, p14808_1]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [hlam, p14808_0]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [h14601, h14683, h14684, hc02, hc34, hlam, hphi, ht23, p14808_1]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                rcases p14808_3 (m.d 0 1) (by simp) with h14841 | h14841
                                · linarith only [h14841, hlam, p14808_0]
                                · rcases p14808_3 (m.d 1 2) (by simp) with h14843 | h14843
                                  · rcases p14808_3 (m.d 1 3) (by simp) with h14844 | h14844
                                    · linarith only [h14799, h14844, hlam]
                                    · linarith only [h10472, h14844, hlam]
                                  · linarith only [h0, h14843, hlam]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [h14683, hlam, p14808_1]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [h10472, hc01, hc15, hlam, hphi, p14808_1]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [h14801, hlam, p14808_0]
                              · have p14808_0 := h14808c.1
                                have p14808_1 := h14808c.2.1
                                have p14808_2 := h14808c.2.2.1
                                have p14808_3 := h14808c.2.2.2
                                linarith only [hlam, p14808_0]
                            · linarith only [h11379, h14680, h14684, h14807, hlam]
                          · linarith only [h12234, h14680, h14806, hlam]
                    · linarith only [h11379, h12234, h14680, h14682, h14801, hc01, hc12, hlam, hphi]
              · linarith only [h12234, h14680, h14682, h14683, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14856 | h14856
              · linarith only [h12233, h14601, h14682, h14856, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14858 | h14858
                · linarith only [h14676, h14680, h14681, h14682, h14858, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14860 | h14860
                  · linarith only [h10472, h14678, h14858, h14860, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14862 | h14862
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14863 | h14863
                      · linarith only [h0, h12233, h14682, h14858, h14863, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14865 | h14865
                        · linarith only [h10472, h14860, h14865, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14867 | h14867
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14868 | h14868
                            · rcases h1bigk with h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [hlam, p14869_0]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h0, hlam, p14869_0]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h10472, hlam, p14869_0]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h11379, hlam, p14869_0]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h12013, hlam, p14869_0]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h14856, h14863, h14867, hc01, hc34, hlam, hphi, ht12, ht23, p14869_1]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [hlam, p14869_0]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h14856, h14863, h14867, hc13, hc34, hlam, hphi, p14869_1]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h14682, hlam, p14869_0]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h14856, hlam, p14869_0]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h14681, h14856, h14863, h14867, hc01, hc34, hlam, hphi, ht12, ht23, p14869_1]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h14681, hlam, p14869_1]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [hlam, p14869_0]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h14858, hlam, p14869_1]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h14860, hlam, p14869_1]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                rcases p14869_3 (m.d 0 1) (by simp) with h14885 | h14885
                                · linarith only [h14885, hlam, p14869_0]
                                · rcases p14869_3 (m.d 1 2) (by simp) with h14887 | h14887
                                  · linarith only [h14682, h14887, hlam]
                                  · linarith only [h0, h14887, hlam]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p14869_1]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h10472, h14682, h14863, hc01, hc34, hlam, hphi, ht12, ht23, p14869_1]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [hlam, p14869_0]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h12013, h14682, h14863, hc01, hc34, hlam, hphi, ht12, ht23, p14869_1]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                rcases p14869_3 (m.d 0 1) (by simp) with h14894 | h14894
                                · linarith only [h14894, hlam, p14869_0]
                                · rcases p14869_3 (m.d 1 2) (by simp) with h14896 | h14896
                                  · linarith only [h14856, h14896, hlam]
                                  · linarith only [h0, h14896, hlam]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p14869_1]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h10472, h14856, h14863, h14867, hc01, hc34, hlam, hphi, ht12, ht23, p14869_1]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [h14862, hlam, p14869_0]
                              · have p14869_0 := h14869c.1
                                have p14869_1 := h14869c.2.1
                                have p14869_2 := h14869c.2.2.1
                                have p14869_3 := h14869c.2.2.2
                                linarith only [hlam, p14869_0]
                            · linarith only [h11379, h14680, h14682, h14863, h14868, hlam]
                          · linarith only [h12233, h12234, h14867, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h11379, h14680, h14862, hlam]
          · linarith only [h0, h12233, h14681, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14907 | h14907
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14908 | h14908
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14909 | h14909
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14910 | h14910
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14911 | h14911
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14912 | h14912
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14913 | h14913
                      · linarith only [h10472, h12233, h12234, h14676, h14680, h14907, h14910, h14912, h14913, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14915 | h14915
                        · linarith only [h10472, h12233, h12234, h14678, h14680, h14907, h14910, h14912, h14915, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14917 | h14917
                          · linarith only [h12233, h12234, h14680, h14913, h14917, hc23, hc34, hlam, hphi]
                          · linarith only [h12233, h12234, h14907, h14910, h14912, h14917, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h12233, h12234, h14908, h14912, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h10472, h14676, h14910, h14911, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14922 | h14922
                  · linarith only [h10472, h14678, h14910, h14922, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14924 | h14924
                    · linarith only [h12233, h12234, h14680, h14910, h14924, hc23, hc34, hlam, hphi]
                    · linarith only [h12233, h12234, h14908, h14924, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h12233, h12234, h14908, h14909, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14928 | h14928
              · linarith only [h12233, h14601, h14908, h14928, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14930 | h14930
                · linarith only [h10472, h14676, h14907, h14908, h14930, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14932 | h14932
                  · linarith only [h10472, h14678, h14930, h14932, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14934 | h14934
                    · linarith only [h12233, h12234, h14680, h14930, h14934, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14936 | h14936
                      · linarith only [h11379, h12233, h12234, h14934, h14936, hc34, hc45, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14938 | h14938
                        · linarith only [h10472, h11379, h12233, h12234, h14932, h14934, h14938, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14940 | h14940
                          · linarith only [h11379, h14934, h14936, h14940, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h12233, h12234, h14940, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h12233, h12234, h14907, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 0 2 4 (by decide) (by decide) with h12234 | h12234
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x1 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234

set_option maxHeartbeats 8040000 in
set_option maxHeartbeats 8040000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s15_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  exact r1l7_11_13_25_L_I_L_I_M_IR_s16 m hb1 hb3 hb5 h0 h10472 h11379 h12013 h12233

set_option maxHeartbeats 8040000 in
set_option maxHeartbeats 8040000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s15_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h12233 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h14944 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  rcases m.htr 0 2 5 (by decide) (by decide) with h14945 | h14945
  · rcases m.htr 0 3 4 (by decide) (by decide) with h14946 | h14946
    · rcases m.htr 0 3 5 (by decide) (by decide) with h14947 | h14947
      · rcases m.htr 0 4 5 (by decide) (by decide) with h14948 | h14948
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14949 | h14949
          · linarith only [h12233, h14945, h14949, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14951 | h14951
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14952 | h14952
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14953 | h14953
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14954 | h14954
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14955 | h14955
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14956 | h14956
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14957 | h14957
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14958 | h14958
                          · linarith only [h0, h14944, h14949, h14958, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14960 | h14960
                            · linarith only [h14956, h14958, h14960, hlam]
                            · rcases h1bigk with h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c | h14962c
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [hlam, p14962_0]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h0, hlam, p14962_0]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h10472, hlam, p14962_0]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h11379, hlam, p14962_0]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h12013, hlam, p14962_0]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h14949, hc01, hc23, hlam, hphi, ht12, p14962_1]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [hlam, p14962_0]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h14949, hlam, p14962_0]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h14949, h14955, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p14962_1, u5ehi1]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h12013, h14949, hc01, hc23, hlam, hphi, ht12, p14962_1]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                rcases p14962_3 (m.d 0 1) (by simp) with h14973 | h14973
                                · linarith only [h14973, hlam, p14962_0]
                                · rcases p14962_3 (m.d 1 2) (by simp) with h14975 | h14975
                                  · linarith only [h14949, h14975, hlam]
                                  · linarith only [h0, h14975, hlam]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h0, hc01, hc13, hlam, hphi, p14962_1]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [hlam, p14962_0]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h11379, h14948, h14949, h14956, h14958, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14962_1]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h12013, h14949, hc01, hc23, hlam, hphi, ht12, p14962_1]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h14949, h14951, hc01, hc23, hlam, hphi, ht12, p14962_1]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h14951, hlam, p14962_1]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h14953, hlam, p14962_0]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [hlam, p14962_0]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h12013, h14949, h14951, hc01, hc23, hlam, hphi, ht12, p14962_1]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h14949, h14952, hc01, hc23, hlam, hphi, ht12, p14962_1]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h14952, hlam, p14962_1]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h14954, hlam, p14962_0]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [h14955, hlam, p14962_0]
                              · have p14962_0 := h14962c.1
                                have p14962_1 := h14962c.2.1
                                have p14962_2 := h14962c.2.2.1
                                have p14962_3 := h14962c.2.2.2
                                linarith only [hlam, p14962_0]
                        · linarith only [h0, h14949, h14957, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h14944, h14948, h14949, h14956, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · linarith only [h0, h11379, h14944, h14948, h14955, hc01, hc12, hlam, hphi]
                  · linarith only [h10472, h14947, h14954, hlam]
                · linarith only [h0, h10472, h14944, h14946, h14949, h14953, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h14945, h14952, hlam]
            · linarith only [h0, h14944, h14951, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14999 | h14999
          · linarith only [h12233, h14945, h14999, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15001 | h15001
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15002 | h15002
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15003 | h15003
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15004 | h15004
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15005 | h15005
                    · linarith only [h11379, h14948, h14999, h15001, h15005, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15007 | h15007
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15008 | h15008
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15009 | h15009
                          · linarith only [h0, h14944, h14999, h15009, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15011 | h15011
                            · linarith only [h11379, h15005, h15007, h15011, hc01, hc24, hlam, hphi, ht12]
                            · rcases h1bigk with h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c | h15013c
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [hlam, p15013_0]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h0, hlam, p15013_0]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h10472, hlam, p15013_0]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h11379, hlam, p15013_0]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h12013, hlam, p15013_0]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h14999, hc01, hc23, hlam, hphi, ht12, p15013_1]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [hlam, p15013_0]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h14999, hlam, p15013_0]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h11379, h14999, hc01, hc23, hlam, hphi, ht12, p15013_1]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h11379, h14999, h15005, hc01, hc23, hlam, hphi, ht12, p15013_1]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                rcases p15013_3 (m.d 0 1) (by simp) with h15024 | h15024
                                · linarith only [h15024, hlam, p15013_0]
                                · rcases p15013_3 (m.d 1 2) (by simp) with h15026 | h15026
                                  · linarith only [h14999, h15026, hlam]
                                  · linarith only [h0, h15026, hlam]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h0, h14945, hc13, hlam, hphi, ht01, ht0b, ht5b, p15013_1, u5ehi2]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [hlam, p15013_0]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h11379, hc01, hc13, hlam, hphi, p15013_1]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h11379, h14999, h15005, hc01, hc23, hlam, hphi, ht12, p15013_1]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h15005, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15013_1]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h15001, hlam, p15013_1]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h15003, hlam, p15013_0]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [hlam, p15013_0]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h15005, hlam, p15013_1]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h14999, h15002, hc01, hc23, hlam, hphi, ht12, p15013_1]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h15002, hlam, p15013_1]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h15004, hlam, p15013_0]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [h11379, h14999, h15002, hc01, hc23, hlam, hphi, ht12, p15013_1]
                              · have p15013_0 := h15013c.1
                                have p15013_1 := h15013c.2.1
                                have p15013_2 := h15013c.2.2.1
                                have p15013_3 := h15013c.2.2.2
                                linarith only [hlam, p15013_0]
                        · linarith only [h0, h14999, h15008, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h14945, h14999, h15007, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h10472, h14947, h15004, hlam]
                · linarith only [h0, h10472, h14944, h14946, h14947, h14999, h15003, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · linarith only [h0, h14945, h15002, hlam]
            · linarith only [h0, h14944, h15001, hlam]
      · linarith only [h12233, h14945, h14947, hlam]
    · linarith only [h12233, h14944, h14946, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h15051 | h15051
    · rcases m.htr 0 3 5 (by decide) (by decide) with h15052 | h15052
      · rcases m.htr 0 4 5 (by decide) (by decide) with h15053 | h15053
        · linarith only [h14944, h14945, h15053, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15055 | h15055
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15056 | h15056
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15057 | h15057
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15058 | h15058
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15059 | h15059
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15060 | h15060
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15061 | h15061
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15062 | h15062
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15063 | h15063
                          · linarith only [h14944, h14945, h15053, h15055, h15062, h15063, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15065 | h15065
                            · linarith only [h14944, h14945, h15061, h15063, h15065, hlam]
                            · rcases h1bigk with h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [hlam, p15067_0]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [h0, hlam, p15067_0]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [h10472, hlam, p15067_0]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [h11379, hlam, p15067_0]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [h12013, hlam, p15067_0]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                rcases p15067_3 (m.d 0 1) (by simp) with h15073 | h15073
                                · linarith only [h15073, hlam, p15067_0]
                                · rcases p15067_3 (m.d 1 2) (by simp) with h15075 | h15075
                                  · rcases p15067_3 (m.d 1 3) (by simp) with h15076 | h15076
                                    · linarith only [h15055, h15076, hlam]
                                    · linarith only [h10472, h15076, hlam]
                                  · linarith only [h15075, hlam, p15067_0]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [hlam, p15067_0]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [h14945, h15058, h15060, h15063, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p15067_1]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [h14944, h14945, h15060, h15061, h15063, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15067_1]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [h14944, h14945, h15060, h15061, h15063, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15067_1]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                rcases p15067_3 (m.d 0 1) (by simp) with h15084 | h15084
                                · linarith only [h15084, hlam, p15067_0]
                                · rcases p15067_3 (m.d 1 2) (by simp) with h15086 | h15086
                                  · rcases p15067_3 (m.d 1 3) (by simp) with h15087 | h15087
                                    · rcases p15067_3 (m.d 1 4) (by simp) with h15088 | h15088
                                      · linarith only [h15058, h15088, hlam]
                                      · linarith only [h11379, h15088, hlam]
                                    · linarith only [h15087, hlam, p15067_0]
                                  · linarith only [h0, h15086, hlam]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [h15055, hlam, p15067_1]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [hlam, p15067_0]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [h14944, h14945, h15060, h15061, h15063, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15067_1]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [h14944, h14945, h15055, h15060, h15061, h15063, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15067_1]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                rcases p15067_3 (m.d 0 1) (by simp) with h15097 | h15097
                                · linarith only [h15097, hlam, p15067_0]
                                · rcases p15067_3 (m.d 1 2) (by simp) with h15099 | h15099
                                  · rcases p15067_3 (m.d 1 3) (by simp) with h15100 | h15100
                                    · rcases p15067_3 (m.d 1 4) (by simp) with h15101 | h15101
                                      · rcases p15067_3 (m.d 1 5) (by simp) with h15102 | h15102
                                        · linarith only [h15060, h15102, hlam]
                                        · linarith only [h12013, h15102, hlam]
                                      · linarith only [h15101, hlam, p15067_0]
                                    · linarith only [h10472, h15100, hlam]
                                  · linarith only [h0, h15099, hlam]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [h15056, hlam, p15067_1]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [h15058, hlam, p15067_0]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [hlam, p15067_0]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [h14944, h14945, h15060, h15061, h15063, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15067_1]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                rcases p15067_3 (m.d 0 1) (by simp) with h15112 | h15112
                                · linarith only [h15112, hlam, p15067_0]
                                · rcases p15067_3 (m.d 1 2) (by simp) with h15114 | h15114
                                  · rcases p15067_3 (m.d 1 3) (by simp) with h15115 | h15115
                                    · rcases p15067_3 (m.d 1 4) (by simp) with h15116 | h15116
                                      · rcases p15067_3 (m.d 1 5) (by simp) with h15117 | h15117
                                        · rcases h1emax with h15118 | h15118 | h15118 | h15118 | h15118
                                          · rcases h3bigk with h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c | h15119c
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [hlam, p15119_0]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [h10472, hlam, p15119_1]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [h12233, hlam, p15119_1]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              rcases p15119_3 (m.d 0 3) (by simp) with h15123 | h15123
                                              · rcases p15119_3 (m.d 1 3) (by simp) with h15124 | h15124
                                                · rcases p15119_3 (m.d 2 3) (by simp) with h15125 | h15125
                                                  · rcases p15119_3 (m.d 3 4) (by simp) with h15126 | h15126
                                                    · linarith only [h15126, hlam, p15119_0]
                                                    · rcases p15119_3 (m.d 3 5) (by simp) with h15128 | h15128
                                                      · linarith only [h15052, h15128, hlam]
                                                      · linarith only [h15065, h15128, hlam]
                                                  · linarith only [h15061, h15125, hlam]
                                                · linarith only [h15058, h15124, hlam]
                                              · linarith only [h15123, hlam, p15119_0]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [h12233, h15055, hc12, hlam, hphi, ht01, ht0b, ht5b, p15119_1, u5ehi3]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [h15052, h15055, hc12, hlam, hphi, ht01, ht0b, ht5b, p15119_1, u5ehi3]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [hlam, p15119_0]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [h12233, h14944, h15055, h15061, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15119_1]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [h14944, h14945, h15058, h15060, h15061, h15063, hlam, p15119_2]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              rcases p15119_3 (m.d 0 3) (by simp) with h15139 | h15139
                                              · linarith only [h10472, h15139, hlam]
                                              · linarith only [h15052, h15139, hlam]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [h15052, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p15119_1, u5ehi3]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [h15055, hlam, p15119_0]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [hlam, p15119_0]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              rcases p15119_3 (m.d 0 3) (by simp) with h15145 | h15145
                                              · linarith only [h12233, h15145, hlam]
                                              · linarith only [h15051, h15145, hlam]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [h15055, hc12, hlam, hphi, ht01, ht0b, ht5b, p15119_1, u5ehi3]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [h15051, hlam, p15119_0]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [h15058, hlam, p15119_0]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [h15061, hlam, p15119_0]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [hlam, p15119_0]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [h15065, hlam, p15119_1]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [h15052, hlam, p15119_0]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [h15059, hlam, p15119_0]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [h15062, hlam, p15119_0]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [h12233, h15052, h15055, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15119_1]
                                            · have p15119_0 := h15119c.1
                                              have p15119_1 := h15119c.2.1
                                              have p15119_2 := h15119c.2.2.1
                                              have p15119_3 := h15119c.2.2.2
                                              linarith only [hlam, p15119_0]
                                          · linarith only [h0, h15118, hc01, hlam]
                                          · linarith only [h14944, h14945, h15058, h15060, h15061, h15063, h15118, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                          · linarith only [h14944, h14945, h15060, h15061, h15063, h15118, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                          · linarith only [h15118, hc01, hlam, p15067_1]
                                        · linarith only [h15117, hlam, p15067_0]
                                      · linarith only [h11379, h15116, hlam]
                                    · linarith only [h10472, h15115, hlam]
                                  · linarith only [h0, h15114, hlam]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [h15057, hlam, p15067_1]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [h15059, hlam, p15067_0]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [h15060, hlam, p15067_0]
                              · have p15067_0 := h15067c.1
                                have p15067_1 := h15067c.2.1
                                have p15067_2 := h15067c.2.2.1
                                have p15067_3 := h15067c.2.2.2
                                linarith only [hlam, p15067_0]
                        · linarith only [h12233, h15052, h15062, hlam]
                      · linarith only [h12233, h15051, h15061, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15173 | h15173
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15174 | h15174
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15175 | h15175
                          · linarith only [h14944, h14945, h15055, h15060, h15174, h15175, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15177 | h15177
                            · linarith only [h11379, h14944, h15060, h15173, h15177, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · rcases h1bigk with h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c | h15179c
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [hlam, p15179_0]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [h0, hlam, p15179_0]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [h10472, hlam, p15179_0]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [h11379, hlam, p15179_0]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [h12013, hlam, p15179_0]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                rcases p15179_3 (m.d 0 1) (by simp) with h15185 | h15185
                                · linarith only [h15185, hlam, p15179_0]
                                · rcases p15179_3 (m.d 1 2) (by simp) with h15187 | h15187
                                  · rcases p15179_3 (m.d 1 3) (by simp) with h15188 | h15188
                                    · linarith only [h15055, h15188, hlam]
                                    · linarith only [h10472, h15188, hlam]
                                  · linarith only [h15187, hlam, p15179_0]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [hlam, p15179_0]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [h14944, h14945, h15057, h15059, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15179_1]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [h11379, hc01, hc12, hlam, hphi, p15179_1]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [h14944, h14945, h15057, h15173, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15179_1]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                rcases p15179_3 (m.d 0 1) (by simp) with h15196 | h15196
                                · linarith only [h15196, hlam, p15179_0]
                                · rcases p15179_3 (m.d 1 2) (by simp) with h15198 | h15198
                                  · rcases p15179_3 (m.d 1 3) (by simp) with h15199 | h15199
                                    · rcases p15179_3 (m.d 1 4) (by simp) with h15200 | h15200
                                      · linarith only [h15058, h15200, hlam]
                                      · linarith only [h11379, h15200, hlam]
                                    · linarith only [h15199, hlam, p15179_0]
                                  · linarith only [h0, h15198, hlam]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [h15055, hlam, p15179_1]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [hlam, p15179_0]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [h11379, hc01, hc13, hlam, hphi, p15179_1]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [h14944, h14945, h15055, h15057, h15173, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15179_1]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [h15060, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15179_1]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [h15056, hlam, p15179_1]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [h15058, hlam, p15179_0]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [hlam, p15179_0]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [h15060, hlam, p15179_1]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                rcases p15179_3 (m.d 0 1) (by simp) with h15214 | h15214
                                · linarith only [h15214, hlam, p15179_0]
                                · rcases p15179_3 (m.d 1 2) (by simp) with h15216 | h15216
                                  · rcases p15179_3 (m.d 1 3) (by simp) with h15217 | h15217
                                    · rcases p15179_3 (m.d 1 4) (by simp) with h15218 | h15218
                                      · linarith only [h15060, h15218, hlam]
                                      · linarith only [h11379, h15218, hlam]
                                    · linarith only [h10472, h15217, hlam]
                                  · linarith only [h0, h15216, hlam]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [h15057, hlam, p15179_1]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [h15059, hlam, p15179_0]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [h11379, hc01, hc15, hlam, hphi, p15179_1]
                              · have p15179_0 := h15179c.1
                                have p15179_1 := h15179c.2.1
                                have p15179_2 := h15179c.2.2.1
                                have p15179_3 := h15179c.2.2.2
                                linarith only [hlam, p15179_0]
                        · linarith only [h12233, h15052, h15174, hlam]
                      · linarith only [h12233, h15051, h15173, hlam]
                  · linarith only [h10472, h12233, h15052, h15059, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h12233, h14944, h15051, h15055, h15058, hlam]
              · linarith only [h12233, h14944, h15055, h15057, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h12233, h14944, h15055, h15056, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15233 | h15233
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15234 | h15234
              · linarith only [h14945, h15055, h15234, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15236 | h15236
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15237 | h15237
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15238 | h15238
                    · linarith only [h11379, h15053, h15055, h15233, h15238, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15240 | h15240
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15241 | h15241
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15242 | h15242
                          · linarith only [h11379, h15238, h15242, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15244 | h15244
                            · linarith only [h0, h14944, h15234, h15240, h15242, h15244, hlam]
                            · rcases h1bigk with h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c | h15246c
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [hlam, p15246_0]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h0, hlam, p15246_0]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h10472, hlam, p15246_0]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h11379, hlam, p15246_0]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h12013, hlam, p15246_0]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h15234, h15242, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15246_1]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [hlam, p15246_0]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h15055, hlam, p15246_0]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h11379, h15234, h15242, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15246_1]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h15234, hlam, p15246_0]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                rcases p15246_3 (m.d 0 1) (by simp) with h15257 | h15257
                                · linarith only [h15257, hlam, p15246_0]
                                · rcases p15246_3 (m.d 1 2) (by simp) with h15259 | h15259
                                  · linarith only [h15055, h15259, hlam]
                                  · linarith only [h0, h15259, hlam]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h0, h15055, hc01, hc23, hlam, hphi, ht12, p15246_1]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [hlam, p15246_0]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h11379, h15055, hc01, hc23, hlam, hphi, ht12, p15246_1]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h12013, h15055, hc01, hc23, hlam, hphi, ht12, p15246_1]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h15055, h15233, hc01, hc23, hlam, hphi, ht12, p15246_1]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h15233, hlam, p15246_1]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h15236, hlam, p15246_0]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [hlam, p15246_0]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h15238, hlam, p15246_1]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                rcases p15246_3 (m.d 0 1) (by simp) with h15271 | h15271
                                · linarith only [h15271, hlam, p15246_0]
                                · rcases p15246_3 (m.d 1 2) (by simp) with h15273 | h15273
                                  · linarith only [h15234, h15273, hlam]
                                  · linarith only [h0, h15273, hlam]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p15246_1]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h15237, hlam, p15246_0]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [h11379, hc01, hc15, hlam, hphi, p15246_1]
                              · have p15246_0 := h15246c.1
                                have p15246_1 := h15246c.2.1
                                have p15246_2 := h15246c.2.2.1
                                have p15246_3 := h15246c.2.2.2
                                linarith only [hlam, p15246_0]
                        · linarith only [h10472, h15052, h15055, h15241, hlam]
                      · linarith only [h10472, h15051, h15055, h15240, hlam]
                  · linarith only [h10472, h15052, h15237, hlam]
                · linarith only [h10472, h12233, h14944, h15051, h15052, h15236, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · linarith only [h0, h14944, h15233, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h15285 | h15285
        · linarith only [h14944, h14945, h15285, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15287 | h15287
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15288 | h15288
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15289 | h15289
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15290 | h15290
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15291 | h15291
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15292 | h15292
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15293 | h15293
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15294 | h15294
                        · linarith only [h12233, h14944, h15052, h15287, h15294, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h12233, h14944, h15291, h15293, h15294, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h12233, h15051, h15293, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15298 | h15298
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15299 | h15299
                        · linarith only [h10472, h15052, h15287, h15299, hc01, hc12, hlam, hphi]
                        · linarith only [h12233, h14944, h15287, h15291, h15298, h15299, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h12233, h15051, h15298, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15303 | h15303
                    · linarith only [h11379, h15285, h15290, h15291, h15303, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15305 | h15305
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15306 | h15306
                        · linarith only [h15287, h15291, h15306, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15308 | h15308
                          · linarith only [h0, h12013, h14944, h15303, h15308, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15310 | h15310
                            · linarith only [h11379, h12233, h14944, h15287, h15291, h15303, h15305, h15310, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h12233, h14944, h15287, h15291, h15305, h15310, hc34, hc45, hlam, hphi]
                      · linarith only [h12233, h14944, h15051, h15052, h15305, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h12233, h14944, h15051, h15287, h15290, hlam]
              · linarith only [h12233, h14944, h15287, h15289, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h12233, h14944, h15287, h15288, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15317 | h15317
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15318 | h15318
              · linarith only [h14945, h15287, h15318, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15320 | h15320
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15321 | h15321
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15322 | h15322
                    · linarith only [h11379, h15285, h15317, h15318, h15322, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15324 | h15324
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15325 | h15325
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15326 | h15326
                          · linarith only [h12233, h14944, h15052, h15287, h15321, h15322, h15326, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15328 | h15328
                            · linarith only [h12233, h14944, h15052, h15287, h15318, h15321, h15324, h15326, h15328, hc12, hc23, hlam, hphi]
                            · rcases h1bigk with h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c | h15330c
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [hlam, p15330_0]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h0, hlam, p15330_0]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h10472, hlam, p15330_0]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h11379, hlam, p15330_0]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h12013, hlam, p15330_0]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h15318, hc01, hc25, hlam, hphi, ht12, p15330_1]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [hlam, p15330_0]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h15287, hlam, p15330_0]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h11379, h12233, h14944, h15052, h15287, h15318, h15321, h15324, h15326, hc01, hc23, hc34, hc45, hlam, hphi, ht12, p15330_1]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h15318, hlam, p15330_0]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                rcases p15330_3 (m.d 0 1) (by simp) with h15341 | h15341
                                · linarith only [h15341, hlam, p15330_0]
                                · rcases p15330_3 (m.d 1 2) (by simp) with h15343 | h15343
                                  · linarith only [h15287, h15343, hlam]
                                  · linarith only [h0, h15343, hlam]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h0, h15287, hc01, hc23, hlam, hphi, ht12, p15330_1]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [hlam, p15330_0]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h11379, h15287, hc01, hc23, hlam, hphi, ht12, p15330_1]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h12233, h14944, h15052, h15287, h15321, h15324, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15330_1]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h15287, h15317, hc01, hc23, hlam, hphi, ht12, p15330_1]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h15317, hlam, p15330_1]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h15320, hlam, p15330_0]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [hlam, p15330_0]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h15322, hlam, p15330_1]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                rcases p15330_3 (m.d 0 1) (by simp) with h15355 | h15355
                                · linarith only [h15355, hlam, p15330_0]
                                · rcases p15330_3 (m.d 1 2) (by simp) with h15357 | h15357
                                  · linarith only [h15318, h15357, hlam]
                                  · linarith only [h0, h15357, hlam]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p15330_1]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h15321, hlam, p15330_0]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [h11379, h15318, h15326, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15330_1]
                              · have p15330_0 := h15330c.1
                                have p15330_1 := h15330c.2.1
                                have p15330_2 := h15330c.2.2.1
                                have p15330_3 := h15330c.2.2.2
                                linarith only [hlam, p15330_0]
                        · linarith only [h15287, h15321, h15325, hlam]
                      · linarith only [h12233, h14944, h15052, h15287, h15321, h15324, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15366 | h15366
                    · linarith only [h11379, h15285, h15287, h15317, h15321, h15366, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15368 | h15368
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15369 | h15369
                        · linarith only [h0, h15287, h15321, h15369, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h11379, h15287, h15317, h15369, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h11379, h15287, h15317, h15368, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h10472, h12233, h14944, h15051, h15320, hlam]
            · linarith only [h0, h10472, h12233, h14944, h15317, hc01, hc13, hlam, hphi]
    · linarith only [h12233, h14944, h15051, hlam]

end R2N4
