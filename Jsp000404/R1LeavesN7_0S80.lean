import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13704000 in
set_option maxHeartbeats 13704000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s39_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h41027 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h45992 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h46639 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h39227 := hg39227
  rcases m.htr 0 3 4 (by decide) (by decide) with h46640 | h46640
  · rcases m.htr 0 3 5 (by decide) (by decide) with h46641 | h46641
    · rcases m.htr 0 4 5 (by decide) (by decide) with h46642 | h46642
      · rcases m.htr 1 2 3 (by decide) (by decide) with h46643 | h46643
        · rcases m.htr 1 2 4 (by decide) (by decide) with h46644 | h46644
          · rcases m.htr 1 2 5 (by decide) (by decide) with h46645 | h46645
            · rcases m.htr 1 3 4 (by decide) (by decide) with h46646 | h46646
              · rcases m.htr 1 3 5 (by decide) (by decide) with h46647 | h46647
                · rcases m.htr 1 4 5 (by decide) (by decide) with h46648 | h46648
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h46649 | h46649
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h46650 | h46650
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h46651 | h46651
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h46652 | h46652
                          · rcases h1bigk with h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c | h46653c
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [hlam, p46653_0]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [h0, hlam, p46653_0]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [h33187, hlam, p46653_0]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [h36828, hlam, p46653_0]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [h39227, hlam, p46653_0]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              rcases p46653_3 (m.d 0 1) (by simp) with h46659 | h46659
                              · linarith only [h46659, hlam, p46653_0]
                              · rcases p46653_3 (m.d 1 2) (by simp) with h46661 | h46661
                                · rcases p46653_3 (m.d 1 3) (by simp) with h46662 | h46662
                                  · linarith only [h46643, h46662, hlam]
                                  · linarith only [h33187, h46662, hlam]
                                · linarith only [h46661, hlam, p46653_0]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [hlam, p46653_0]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [h39227, h45992, h46639, h46644, h46646, hc01, hc12, hlam, hphi, p46653_1]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [h45992, h46639, h46644, h46650, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p46653_1]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [h39227, hc01, hc12, hlam, hphi, p46653_1]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              rcases p46653_3 (m.d 0 1) (by simp) with h46670 | h46670
                              · linarith only [h46670, hlam, p46653_0]
                              · rcases p46653_3 (m.d 1 2) (by simp) with h46672 | h46672
                                · rcases p46653_3 (m.d 1 3) (by simp) with h46673 | h46673
                                  · rcases p46653_3 (m.d 1 4) (by simp) with h46674 | h46674
                                    · linarith only [h46646, h46674, hlam]
                                    · linarith only [h36828, h46674, hlam]
                                  · linarith only [h46673, hlam, p46653_0]
                                · linarith only [h0, h46672, hlam]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [h46643, hlam, p46653_0]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [hlam, p46653_0]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [h45992, h46639, h46644, h46650, h46652, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p46653_1]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [h39227, h46643, hc01, hc12, hlam, hphi, p46653_1]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              rcases p46653_3 (m.d 0 1) (by simp) with h46683 | h46683
                              · linarith only [h46683, hlam, p46653_0]
                              · rcases p46653_3 (m.d 1 2) (by simp) with h46685 | h46685
                                · rcases p46653_3 (m.d 1 3) (by simp) with h46686 | h46686
                                  · rcases p46653_3 (m.d 1 4) (by simp) with h46687 | h46687
                                    · rcases p46653_3 (m.d 1 5) (by simp) with h46688 | h46688
                                      · linarith only [h46648, h46688, hlam]
                                      · linarith only [h39227, h46688, hlam]
                                    · linarith only [h46687, hlam, p46653_0]
                                  · linarith only [h33187, h46686, hlam]
                                · linarith only [h0, h46685, hlam]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [h46644, hlam, p46653_0]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [h46646, hlam, p46653_1]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [hlam, p46653_0]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [h39227, hc01, hc14, hlam, hphi, p46653_1]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              rcases p46653_3 (m.d 0 1) (by simp) with h46698 | h46698
                              · linarith only [h46698, hlam, p46653_0]
                              · rcases p46653_3 (m.d 1 2) (by simp) with h46700 | h46700
                                · rcases p46653_3 (m.d 1 3) (by simp) with h46701 | h46701
                                  · rcases p46653_3 (m.d 1 4) (by simp) with h46702 | h46702
                                    · rcases p46653_3 (m.d 1 5) (by simp) with h46703 | h46703
                                      · rcases h1emax with h46704 | h46704 | h46704 | h46704 | h46704
                                        · rcases h2bigk with h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c | h46705c
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [hlam, p46705_0]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [h0, hlam, p46705_0]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [h41027, hlam, p46705_0]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [h45992, hlam, p46705_0]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [h41027, h46643, h46650, h46652, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p46705_1]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            rcases p46705_3 (m.d 0 2) (by simp) with h46711 | h46711
                                            · linarith only [h0, h46711, hlam]
                                            · rcases p46705_3 (m.d 1 2) (by simp) with h46713 | h46713
                                              · rcases p46705_3 (m.d 2 3) (by simp) with h46714 | h46714
                                                · linarith only [h46643, h46714, hlam]
                                                · linarith only [h41027, h46714, hlam]
                                              · linarith only [h0, h46713, hlam]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [hlam, p46705_0]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [h0, h45992, h46649, hc01, hc12, hlam, hphi, p46705_1]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [h45992, h46639, h46650, h46652, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p46705_1]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [h41027, h46639, h46643, hlam, p46705_2]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [h46639, h46643, h46650, h46652, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p46705_1]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [h46643, hlam, p46705_0]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [hlam, p46705_0]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [h45992, h46639, h46643, h46650, h46652, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p46705_1]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            rcases p46705_3 (m.d 0 2) (by simp) with h46726 | h46726
                                            · linarith only [h41027, h46726, hlam]
                                            · linarith only [h46639, h46726, hlam]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [h46639, h46644, h46650, h46652, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p46705_1]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [h46644, hlam, p46705_0]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [h46649, hlam, p46705_0]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [hlam, p46705_0]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            rcases p46705_3 (m.d 0 2) (by simp) with h46733 | h46733
                                            · linarith only [h45992, h46733, hlam]
                                            · linarith only [h46639, h46733, hlam]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [h46639, hlam, p46705_0]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [h46645, hlam, p46705_0]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [h46650, hlam, p46705_0]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [h46651, hlam, p46705_1]
                                          · have p46705_0 := h46705c.1
                                            have p46705_1 := h46705c.2.1
                                            have p46705_2 := h46705c.2.2.1
                                            have p46705_3 := h46705c.2.2.2
                                            linarith only [hlam, p46705_0]
                                        · linarith only [h0, h46704, hc01, hlam]
                                        · linarith only [h46646, h46648, h46704, hc01, hlam, p46653_1]
                                        · linarith only [h46648, h46704, hc01, hlam, p46653_1]
                                        · linarith only [h46704, hc01, hlam, p46653_1]
                                      · linarith only [h46703, hlam, p46653_0]
                                    · linarith only [h36828, h46702, hlam]
                                  · linarith only [h33187, h46701, hlam]
                                · linarith only [h0, h46700, hlam]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [h46645, hlam, p46653_0]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [h46647, hlam, p46653_0]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [h46648, hlam, p46653_0]
                            · have p46653_0 := h46653c.1
                              have p46653_1 := h46653c.2.1
                              have p46653_2 := h46653c.2.2.1
                              have p46653_3 := h46653c.2.2.2
                              linarith only [hlam, p46653_0]
                          · linarith only [h45992, h46639, h46643, h46649, h46651, h46652, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h45992, h46639, h46642, h46651, hc04, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h41027, h46641, h46650, hlam]
                    · linarith only [h41027, h46640, h46649, hlam]
                  · linarith only [h45992, h46639, h46642, h46644, h46648, hlam]
                · linarith only [h45992, h46639, h46641, h46644, h46646, h46647, hlam]
              · linarith only [h41027, h46640, h46643, h46646, hlam]
            · linarith only [h41027, h45992, h46639, h46643, h46644, h46645, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · linarith only [h41027, h46643, h46644, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h46762 | h46762
          · linarith only [h45992, h46639, h46643, h46762, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h46764 | h46764
            · rcases m.htr 1 3 4 (by decide) (by decide) with h46765 | h46765
              · rcases m.htr 1 3 5 (by decide) (by decide) with h46766 | h46766
                · rcases m.htr 1 4 5 (by decide) (by decide) with h46767 | h46767
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h46768 | h46768
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h46769 | h46769
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h46770 | h46770
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h46771 | h46771
                          · rcases h1bigk with h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c | h46772c
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [hlam, p46772_0]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h0, hlam, p46772_0]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h33187, hlam, p46772_0]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h36828, hlam, p46772_0]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h39227, hlam, p46772_0]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h46762, h46768, hc01, hc23, hlam, hphi, ht12, p46772_1]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [hlam, p46772_0]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h46643, hlam, p46772_1]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h46762, hlam, p46772_1]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h39227, h46762, h46768, hc01, hc23, hlam, hphi, ht12, p46772_1]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              rcases p46772_3 (m.d 0 1) (by simp) with h46783 | h46783
                              · linarith only [h46783, hlam, p46772_0]
                              · rcases p46772_3 (m.d 1 2) (by simp) with h46785 | h46785
                                · linarith only [h46643, h46785, hlam]
                                · linarith only [h0, h46785, hlam]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h0, h46643, hc01, hc23, hlam, hphi, ht12, p46772_1]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [hlam, p46772_0]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h36828, h46643, hc01, hc23, hlam, hphi, ht12, p46772_1]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h39227, h46643, hc01, hc23, hlam, hphi, ht12, p46772_1]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              rcases p46772_3 (m.d 0 1) (by simp) with h46792 | h46792
                              · linarith only [h46792, hlam, p46772_0]
                              · rcases p46772_3 (m.d 1 2) (by simp) with h46794 | h46794
                                · linarith only [h46762, h46794, hlam]
                                · linarith only [h0, h46794, hlam]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h39227, h46764, hc01, hc14, hlam, hphi, p46772_1]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h46765, hlam, p46772_1]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [hlam, p46772_0]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h39227, h46762, h46768, hc01, hc23, hlam, hphi, ht12, p46772_1]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h46643, h46764, hc01, hc23, hlam, hphi, ht12, p46772_1]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h46764, hlam, p46772_0]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h46766, hlam, p46772_0]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [h46767, hlam, p46772_0]
                            · have p46772_0 := h46772c.1
                              have p46772_1 := h46772c.2.1
                              have p46772_2 := h46772c.2.2.1
                              have p46772_3 := h46772c.2.2.2
                              linarith only [hlam, p46772_0]
                          · rcases h1bigk with h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c | h46806c
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [hlam, p46806_0]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h0, hlam, p46806_0]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h33187, hlam, p46806_0]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h36828, hlam, p46806_0]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h39227, hlam, p46806_0]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h46762, h46768, hc01, hc23, hlam, hphi, ht12, p46806_1]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [hlam, p46806_0]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h46643, hlam, p46806_1]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h46762, hlam, p46806_1]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h39227, h46762, h46768, hc01, hc23, hlam, hphi, ht12, p46806_1]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              rcases p46806_3 (m.d 0 1) (by simp) with h46817 | h46817
                              · linarith only [h46817, hlam, p46806_0]
                              · rcases p46806_3 (m.d 1 2) (by simp) with h46819 | h46819
                                · linarith only [h46643, h46819, hlam]
                                · linarith only [h0, h46819, hlam]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h0, h46643, hc01, hc23, hlam, hphi, ht12, p46806_1]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [hlam, p46806_0]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h36828, h46643, hc01, hc23, hlam, hphi, ht12, p46806_1]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h39227, h46643, hc01, hc23, hlam, hphi, ht12, p46806_1]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              rcases p46806_3 (m.d 0 1) (by simp) with h46826 | h46826
                              · linarith only [h46826, hlam, p46806_0]
                              · rcases p46806_3 (m.d 1 2) (by simp) with h46828 | h46828
                                · linarith only [h46762, h46828, hlam]
                                · linarith only [h0, h46828, hlam]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p46806_1]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h46765, hlam, p46806_1]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [hlam, p46806_0]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h39227, h46762, h46768, hc01, hc23, hlam, hphi, ht12, p46806_1]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h46643, h46764, hc01, hc23, hlam, hphi, ht12, p46806_1]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h46764, hlam, p46806_0]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h46766, hlam, p46806_0]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [h46767, hlam, p46806_0]
                            · have p46806_0 := h46806c.1
                              have p46806_1 := h46806c.2.1
                              have p46806_2 := h46806c.2.2.1
                              have p46806_3 := h46806c.2.2.2
                              linarith only [hlam, p46806_0]
                        · linarith only [h0, h46762, h46770, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h39227, h46762, h46764, h46768, h46769, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h33187, h46640, h46643, h46768, hlam]
                  · linarith only [h36828, h46642, h46767, hlam]
                · linarith only [h0, h33187, h46639, h46641, h46762, h46766, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h33187, h46640, h46765, hlam]
            · linarith only [h0, h46639, h46764, hlam]
      · linarith only [h45992, h46639, h46642, hlam]
    · linarith only [h45992, h46639, h46640, h46641, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h46849 | h46849
    · rcases m.htr 0 4 5 (by decide) (by decide) with h46850 | h46850
      · rcases m.htr 1 2 3 (by decide) (by decide) with h46851 | h46851
        · rcases m.htr 1 2 4 (by decide) (by decide) with h46852 | h46852
          · rcases m.htr 1 2 5 (by decide) (by decide) with h46853 | h46853
            · rcases m.htr 1 3 4 (by decide) (by decide) with h46854 | h46854
              · rcases m.htr 1 3 5 (by decide) (by decide) with h46855 | h46855
                · rcases m.htr 1 4 5 (by decide) (by decide) with h46856 | h46856
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h46857 | h46857
                    · linarith only [h41027, h46639, h46640, h46851, h46857, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h41027, h46639, h46851, h46854, h46857, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h36828, h46850, h46856, hlam]
                · linarith only [h33187, h46849, h46855, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h46862 | h46862
                · rcases m.htr 1 4 5 (by decide) (by decide) with h46863 | h46863
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h46864 | h46864
                    · linarith only [h46851, h46854, h46864, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h46866 | h46866
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h46867 | h46867
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h46868 | h46868
                          · rcases h1bigk with h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c | h46869c
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [hlam, p46869_0]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h0, hlam, p46869_0]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h33187, hlam, p46869_0]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h36828, hlam, p46869_0]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h39227, hlam, p46869_0]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              rcases p46869_3 (m.d 0 1) (by simp) with h46875 | h46875
                              · linarith only [h46875, hlam, p46869_0]
                              · rcases p46869_3 (m.d 1 2) (by simp) with h46877 | h46877
                                · rcases p46869_3 (m.d 1 3) (by simp) with h46878 | h46878
                                  · linarith only [h46851, h46878, hlam]
                                  · linarith only [h33187, h46878, hlam]
                                · linarith only [h46877, hlam, p46869_0]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [hlam, p46869_0]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h33187, hc01, hc12, hlam, hphi, p46869_1]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h36828, hc01, hc12, hlam, hphi, p46869_1]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h39227, hc01, hc12, hlam, hphi, p46869_1]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h46854, hc01, hc34, hlam, hphi, ht12, ht23, p46869_1]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h46851, hlam, p46869_0]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [hlam, p46869_0]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h46854, hlam, p46869_0]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h39227, hc01, hc13, hlam, hphi, p46869_1]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              rcases p46869_3 (m.d 0 1) (by simp) with h46891 | h46891
                              · linarith only [h46891, hlam, p46869_0]
                              · rcases p46869_3 (m.d 1 2) (by simp) with h46893 | h46893
                                · rcases p46869_3 (m.d 1 3) (by simp) with h46894 | h46894
                                  · linarith only [h46854, h46894, hlam]
                                  · linarith only [h33187, h46894, hlam]
                                · linarith only [h0, h46893, hlam]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h46852, hlam, p46869_0]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h33187, h46854, hc01, hc34, hlam, hphi, ht12, ht23, p46869_1]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [hlam, p46869_0]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h39227, h46854, hc01, hc34, hlam, hphi, ht12, ht23, p46869_1]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h46854, h46862, hc01, hc34, hlam, hphi, ht12, ht23, p46869_1]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h46853, hlam, p46869_0]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h46862, hlam, p46869_0]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [h46863, hlam, p46869_0]
                            · have p46869_0 := h46869c.1
                              have p46869_1 := h46869c.2.1
                              have p46869_2 := h46869c.2.2.1
                              have p46869_3 := h46869c.2.2.2
                              linarith only [hlam, p46869_0]
                          · linarith only [h33187, h46854, h46868, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h36828, h41027, h45992, h46639, h46850, h46851, h46854, h46867, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h41027, h46639, h46640, h46849, h46866, hc04, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h36828, h41027, h46639, h46850, h46851, h46854, h46863, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h41027, h46639, h46849, h46851, h46862, hlam]
            · linarith only [h41027, h46639, h46853, hc12, hc23, hlam, hphi]
          · linarith only [h41027, h46851, h46852, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h46914 | h46914
          · linarith only [h45992, h46639, h46851, h46914, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h46916 | h46916
            · rcases m.htr 1 3 4 (by decide) (by decide) with h46917 | h46917
              · rcases m.htr 1 3 5 (by decide) (by decide) with h46918 | h46918
                · rcases m.htr 1 4 5 (by decide) (by decide) with h46919 | h46919
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h46920 | h46920
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h46921 | h46921
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h46922 | h46922
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h46923 | h46923
                          · rcases h1bigk with h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c | h46924c
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [hlam, p46924_0]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h0, hlam, p46924_0]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h33187, hlam, p46924_0]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h36828, hlam, p46924_0]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h39227, hlam, p46924_0]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h46914, h46920, hc01, hc23, hlam, hphi, ht12, p46924_1]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [hlam, p46924_0]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h46851, hlam, p46924_1]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h46914, hlam, p46924_1]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h39227, h46914, h46920, hc01, hc23, hlam, hphi, ht12, p46924_1]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              rcases p46924_3 (m.d 0 1) (by simp) with h46935 | h46935
                              · linarith only [h46935, hlam, p46924_0]
                              · rcases p46924_3 (m.d 1 2) (by simp) with h46937 | h46937
                                · linarith only [h46851, h46937, hlam]
                                · linarith only [h0, h46937, hlam]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h0, h46851, hc01, hc23, hlam, hphi, ht12, p46924_1]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [hlam, p46924_0]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h36828, h46851, hc01, hc23, hlam, hphi, ht12, p46924_1]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h39227, h46851, hc01, hc23, hlam, hphi, ht12, p46924_1]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              rcases p46924_3 (m.d 0 1) (by simp) with h46944 | h46944
                              · linarith only [h46944, hlam, p46924_0]
                              · rcases p46924_3 (m.d 1 2) (by simp) with h46946 | h46946
                                · linarith only [h46914, h46946, hlam]
                                · linarith only [h0, h46946, hlam]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h39227, h46916, hc01, hc14, hlam, hphi, p46924_1]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h46917, hlam, p46924_1]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [hlam, p46924_0]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h39227, h46914, h46920, hc01, hc23, hlam, hphi, ht12, p46924_1]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h46851, h46916, hc01, hc23, hlam, hphi, ht12, p46924_1]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h46916, hlam, p46924_0]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h46918, hlam, p46924_0]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [h46919, hlam, p46924_0]
                            · have p46924_0 := h46924c.1
                              have p46924_1 := h46924c.2.1
                              have p46924_2 := h46924c.2.2.1
                              have p46924_3 := h46924c.2.2.2
                              linarith only [hlam, p46924_0]
                          · linarith only [h41027, h46639, h46640, h46850, h46921, h46923, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h46914, h46922, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h41027, h46640, h46851, h46917, h46921, hc02, hc35, hlam, hphi, ht23]
                    · linarith only [h46851, h46917, h46920, hlam]
                  · linarith only [h36828, h41027, h46639, h46640, h46850, h46851, h46917, h46919, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h46640, h46849, h46917, h46918, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h46964 | h46964
                · rcases m.htr 1 4 5 (by decide) (by decide) with h46965 | h46965
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h46966 | h46966
                    · linarith only [h39227, h46851, h46916, h46917, h46966, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h39227, h46851, h46916, h46966, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h36828, h46639, h46850, h46851, h46965, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h33187, h46849, h46964, hlam]
            · linarith only [h0, h33187, h41027, h46639, h46916, hc01, hc13, hlam, hphi]
      · linarith only [h41027, h46639, h46640, h46850, hlam]
    · linarith only [h41027, h46639, h46849, hlam]

end R2N4
