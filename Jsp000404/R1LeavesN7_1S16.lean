import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11673 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h11675 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h11677 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h11679 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  rcases m.htr 1 3 5 (by decide) (by decide) with h11680 | h11680
  · rcases m.htr 1 4 5 (by decide) (by decide) with h11681 | h11681
    · linarith only [h11681, h2, h9967, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h11683 | h11683
      · rcases m.htr 2 3 5 (by decide) (by decide) with h11684 | h11684
        · rcases m.htr 2 4 5 (by decide) (by decide) with h11685 | h11685
          · rcases m.htr 3 4 5 (by decide) (by decide) with h11686 | h11686
            · linarith only [h1, h11679, h11686, h7821, h9967, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h0bigk with h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c | h11688c
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [hlam, p11688_0]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                rcases p11688_3 (m.d 0 1) (by simp) with h11690 | h11690
                · rcases p11688_3 (m.d 0 2) (by simp) with h11691 | h11691
                  · linarith only [h0, h11691, hlam]
                  · rcases p11688_3 (m.d 0 3) (by simp) with h11693 | h11693
                    · linarith only [h1, h11693, hlam]
                    · linarith only [h11693, h4, hlam]
                · linarith only [h0, h11690, hlam]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                rcases p11688_3 (m.d 0 1) (by simp) with h11697 | h11697
                · rcases p11688_3 (m.d 0 2) (by simp) with h11698 | h11698
                  · linarith only [h0, h11698, hlam]
                  · rcases p11688_3 (m.d 0 3) (by simp) with h11700 | h11700
                    · linarith only [h1, h11700, hlam]
                    · rcases p11688_3 (m.d 0 4) (by simp) with h11702 | h11702
                      · linarith only [h11702, h2, hlam]
                      · rcases p11688_3 (m.d 0 5) (by simp) with h11704 | h11704
                        · linarith only [h11704, h3, hlam]
                        · rcases h2bigk with h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c | h11706c
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [hlam, p11706_0]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [h11683, h11685, h7821, h9967, hc12, hc23, hlam, hphi, p11706_1]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [h4, hlam, p11706_0]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [h7821, hlam, p11706_0]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [h9029, hlam, p11706_0]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [h0, hlam, p11706_0]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [hlam, p11706_0]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [h11673, hlam, p11706_0]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [h11675, hlam, p11706_0]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [h11677, hlam, p11706_0]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            rcases p11706_3 (m.d 0 2) (by simp) with h11717 | h11717
                            · linarith only [h11717, hlam, p11706_0]
                            · rcases p11706_3 (m.d 1 2) (by simp) with h11719 | h11719
                              · linarith only [h11673, h11719, hlam]
                              · rcases p11706_3 (m.d 2 3) (by simp) with h11721 | h11721
                                · rcases p11706_3 (m.d 2 4) (by simp) with h11722 | h11722
                                  · linarith only [h11683, h11722, hlam]
                                  · linarith only [h11722, h7821, hlam]
                                · linarith only [h11721, hlam, p11706_0]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            rcases p11706_3 (m.d 0 2) (by simp) with h11726 | h11726
                            · linarith only [h11726, h4, hlam]
                            · linarith only [h0, h11726, hlam]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [hlam, p11706_0]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [h11685, h7821, h9967, hc02, hc23, hlam, hphi, p11706_1]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [h0, h9029, hc12, hc23, hlam, hphi, p11706_1]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            rcases p11706_3 (m.d 0 2) (by simp) with h11732 | h11732
                            · linarith only [h11732, hlam, p11706_0]
                            · rcases p11706_3 (m.d 1 2) (by simp) with h11734 | h11734
                              · linarith only [h11675, h11734, hlam]
                              · rcases p11706_3 (m.d 2 3) (by simp) with h11736 | h11736
                                · rcases p11706_3 (m.d 2 4) (by simp) with h11737 | h11737
                                  · rcases p11706_3 (m.d 2 5) (by simp) with h11738 | h11738
                                    · linarith only [h11685, h11738, hlam]
                                    · linarith only [h11738, h9029, hlam]
                                  · linarith only [h11737, hlam, p11706_0]
                                · linarith only [h11736, h4, hlam]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            rcases p11706_3 (m.d 0 2) (by simp) with h11743 | h11743
                            · linarith only [h11743, h7821, hlam]
                            · linarith only [h0, h11743, hlam]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [h11683, hlam, p11706_1]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [hlam, p11706_0]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [h0, h11685, h7821, h9967, hc12, hc24, hlam, hphi, p11706_1]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            rcases p11706_3 (m.d 0 2) (by simp) with h11749 | h11749
                            · linarith only [h11749, hlam, p11706_0]
                            · rcases p11706_3 (m.d 1 2) (by simp) with h11751 | h11751
                              · linarith only [h11677, h11751, hlam]
                              · rcases p11706_3 (m.d 2 3) (by simp) with h11753 | h11753
                                · rcases p11706_3 (m.d 2 4) (by simp) with h11754 | h11754
                                  · rcases p11706_3 (m.d 2 5) (by simp) with h11755 | h11755
                                    · rcases h3bigk with h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c | h11756c
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [hlam, p11756_0]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p11688_1, p11756_1]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [h4, hlam, p11756_1]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11688_1, p11756_1]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [hc01, hc35, hlam, hphi, ht0b, ht5b, p11688_1, p11756_1]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [h1, hlam, p11756_0]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [hlam, p11756_0]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [h11673, hlam, p11756_1]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11688_1, p11756_1]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p11688_1, p11756_1]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        rcases p11756_3 (m.d 0 3) (by simp) with h11767 | h11767
                                        · linarith only [h11767, h4, hlam]
                                        · rcases p11756_3 (m.d 1 3) (by simp) with h11769 | h11769
                                          · linarith only [h11673, h11769, hlam]
                                          · rcases p11756_3 (m.d 2 3) (by simp) with h11771 | h11771
                                            · rcases p11756_3 (m.d 3 4) (by simp) with h11772 | h11772
                                              · linarith only [h11683, h11772, hlam]
                                              · rcases p11756_3 (m.d 3 5) (by simp) with h11774 | h11774
                                                · linarith only [h11684, h11774, hlam]
                                                · rcases h5bigk with h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c | h11776c
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [hlam, p11776_0]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h9966, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p11756_1, p11776_1]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h9029, hlam, p11776_0]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h11686, h9966, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11756_1, p11776_1]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h9967, hlam, p11776_1]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h3, hlam, p11776_0]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [hlam, p11776_0]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h11677, hlam, p11776_0]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h11686, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11776_1]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h11681, hlam, p11776_1]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h0, h9029, hc12, hc25, hlam, hphi, p11776_1]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h11677, hc12, hc25, hlam, hphi, p11776_1]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [hlam, p11776_0]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    rcases p11776_3 (m.d 0 5) (by simp) with h11790 | h11790
                                                    · linarith only [h11790, h9029, hlam]
                                                    · linarith only [h11790, h9966, hlam]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h0, h11683, h11685, h7821, h9967, hc12, hc23, hlam, hphi, p11776_1]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h9966, hlam, p11776_0]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h11680, hlam, p11776_0]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h11684, hlam, p11776_0]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [hlam, p11776_0]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h11686, hlam, p11776_1]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h0, h7821, h9967, hc12, hc45, hlam, hphi, ht23, ht34, p11776_1]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h1, h11675, h11680, h11681, h11686, hc12, hc23, hc34, hc45, hlam, hphi, p11756_1, p11776_1]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h11685, hlam, p11776_0]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [h11683, h11685, h11686, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11776_1]
                                                  · have p11776_0 := h11776c.1
                                                    have p11776_1 := h11776c.2.1
                                                    have p11776_2 := h11776c.2.2.1
                                                    have p11776_3 := h11776c.2.2.2
                                                    linarith only [hlam, p11776_0]
                                            · linarith only [h11771, h4, hlam]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        rcases p11756_3 (m.d 0 3) (by simp) with h11805 | h11805
                                        · linarith only [h11805, h4, hlam]
                                        · linarith only [h1, h11805, hlam]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [hlam, p11756_0]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        rcases p11756_3 (m.d 0 3) (by simp) with h11809 | h11809
                                        · linarith only [h11809, h4, hlam]
                                        · linarith only [h11809, h9965, hlam]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        rcases p11756_3 (m.d 0 3) (by simp) with h11812 | h11812
                                        · linarith only [h11812, h4, hlam]
                                        · linarith only [h11812, h9966, hlam]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [h9965, hlam, p11756_0]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [h11679, hlam, p11756_0]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [h11683, hlam, p11756_0]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [hlam, p11756_0]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [h11686, hlam, p11756_1]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [h9966, hlam, p11756_0]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [h11680, hlam, p11756_0]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [h11684, hlam, p11756_0]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [h1, h11680, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11688_1, p11756_1]
                                      · have p11756_0 := h11756c.1
                                        have p11756_1 := h11756c.2.1
                                        have p11756_2 := h11756c.2.2.1
                                        have p11756_3 := h11756c.2.2.2
                                        linarith only [hlam, p11756_0]
                                    · linarith only [h11755, hlam, p11706_0]
                                  · linarith only [h11754, h7821, hlam]
                                · linarith only [h11753, h4, hlam]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            rcases p11706_3 (m.d 0 2) (by simp) with h11828 | h11828
                            · linarith only [h11828, h9029, hlam]
                            · linarith only [h0, h11828, hlam]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [h11684, hlam, p11706_1]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [h11685, hlam, p11706_0]
                          · have p11706_0 := h11706c.1
                            have p11706_1 := h11706c.2.1
                            have p11706_2 := h11706c.2.2.1
                            have p11706_3 := h11706c.2.2.2
                            linarith only [hlam, p11706_0]
                · linarith only [h1, h11697, hlam]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                rcases p11688_3 (m.d 0 1) (by simp) with h11835 | h11835
                · rcases p11688_3 (m.d 0 2) (by simp) with h11836 | h11836
                  · linarith only [h0, h11836, hlam]
                  · rcases p11688_3 (m.d 0 3) (by simp) with h11838 | h11838
                    · linarith only [h1, h11838, hlam]
                    · linarith only [h11838, h9965, hlam]
                · linarith only [h11835, h2, hlam]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                rcases p11688_3 (m.d 0 1) (by simp) with h11842 | h11842
                · rcases p11688_3 (m.d 0 2) (by simp) with h11843 | h11843
                  · linarith only [h0, h11843, hlam]
                  · rcases p11688_3 (m.d 0 3) (by simp) with h11845 | h11845
                    · linarith only [h1, h11845, hlam]
                    · linarith only [h11845, h9966, hlam]
                · linarith only [h11842, h3, hlam]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [h0, hlam, p11688_0]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [hlam, p11688_0]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [h4, hlam, p11688_0]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [h7821, hlam, p11688_1]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [h9029, hlam, p11688_0]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [h1, hlam, p11688_1]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                rcases p11688_3 (m.d 0 1) (by simp) with h11855 | h11855
                · rcases p11688_3 (m.d 0 2) (by simp) with h11856 | h11856
                  · linarith only [h11856, h4, hlam]
                  · rcases p11688_3 (m.d 0 3) (by simp) with h11858 | h11858
                    · rcases p11688_3 (m.d 0 4) (by simp) with h11859 | h11859
                      · linarith only [h11859, h9965, hlam]
                      · linarith only [h11859, h7821, hlam]
                    · linarith only [h11858, h4, hlam]
                · linarith only [h0, h11855, hlam]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [hlam, p11688_0]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                rcases p11688_3 (m.d 0 1) (by simp) with h11865 | h11865
                · rcases p11688_3 (m.d 0 2) (by simp) with h11866 | h11866
                  · linarith only [h11866, h4, hlam]
                  · rcases p11688_3 (m.d 0 3) (by simp) with h11868 | h11868
                    · rcases p11688_3 (m.d 0 4) (by simp) with h11869 | h11869
                      · linarith only [h11869, h9965, hlam]
                      · rcases p11688_3 (m.d 0 5) (by simp) with h11871 | h11871
                        · linarith only [h11871, h9966, hlam]
                        · linarith only [h11871, h9967, hlam]
                    · linarith only [h11868, h9965, hlam]
                · linarith only [h11865, h2, hlam]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                rcases p11688_3 (m.d 0 1) (by simp) with h11876 | h11876
                · rcases p11688_3 (m.d 0 2) (by simp) with h11877 | h11877
                  · linarith only [h11877, h4, hlam]
                  · rcases p11688_3 (m.d 0 3) (by simp) with h11879 | h11879
                    · rcases p11688_3 (m.d 0 4) (by simp) with h11880 | h11880
                      · linarith only [h11880, h9965, hlam]
                      · rcases p11688_3 (m.d 0 5) (by simp) with h11882 | h11882
                        · linarith only [h11882, h9966, hlam]
                        · rcases h2bigk with h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c | h11884c
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [hlam, p11884_0]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p11884_1]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [h4, hlam, p11884_0]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [h7821, hlam, p11884_0]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [h9029, hlam, p11884_0]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [h0, hlam, p11884_0]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [hlam, p11884_0]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [h11673, hlam, p11884_0]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [h11675, hlam, p11884_0]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [h11677, hlam, p11884_0]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            rcases p11884_3 (m.d 0 2) (by simp) with h11895 | h11895
                            · linarith only [h11895, hlam, p11884_0]
                            · rcases p11884_3 (m.d 1 2) (by simp) with h11897 | h11897
                              · linarith only [h11673, h11897, hlam]
                              · rcases p11884_3 (m.d 2 3) (by simp) with h11899 | h11899
                                · rcases p11884_3 (m.d 2 4) (by simp) with h11900 | h11900
                                  · linarith only [h11683, h11900, hlam]
                                  · linarith only [h11900, h7821, hlam]
                                · linarith only [h11899, hlam, p11884_0]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            rcases p11884_3 (m.d 0 2) (by simp) with h11904 | h11904
                            · linarith only [h11904, h4, hlam]
                            · linarith only [h0, h11904, hlam]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [hlam, p11884_0]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [h7821, hc02, hc23, hlam, hphi, p11884_1]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [h0, h9029, hc12, hc23, hlam, hphi, p11884_1]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            rcases p11884_3 (m.d 0 2) (by simp) with h11910 | h11910
                            · linarith only [h11910, hlam, p11884_0]
                            · rcases p11884_3 (m.d 1 2) (by simp) with h11912 | h11912
                              · linarith only [h11675, h11912, hlam]
                              · rcases p11884_3 (m.d 2 3) (by simp) with h11914 | h11914
                                · rcases p11884_3 (m.d 2 4) (by simp) with h11915 | h11915
                                  · rcases p11884_3 (m.d 2 5) (by simp) with h11916 | h11916
                                    · linarith only [h11685, h11916, hlam]
                                    · linarith only [h11916, h9029, hlam]
                                  · linarith only [h11915, hlam, p11884_0]
                                · linarith only [h11914, h4, hlam]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            rcases p11884_3 (m.d 0 2) (by simp) with h11921 | h11921
                            · linarith only [h11921, h7821, hlam]
                            · linarith only [h0, h11921, hlam]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [h11683, hlam, p11884_1]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [hlam, p11884_0]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [h11675, h11685, h2, h9967, hc12, hc24, hlam, hphi, p11884_1]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            rcases p11884_3 (m.d 0 2) (by simp) with h11927 | h11927
                            · linarith only [h11927, hlam, p11884_0]
                            · rcases p11884_3 (m.d 1 2) (by simp) with h11929 | h11929
                              · linarith only [h11677, h11929, hlam]
                              · rcases p11884_3 (m.d 2 3) (by simp) with h11931 | h11931
                                · rcases p11884_3 (m.d 2 4) (by simp) with h11932 | h11932
                                  · rcases p11884_3 (m.d 2 5) (by simp) with h11933 | h11933
                                    · rcases h3bigk with h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c | h11934c
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        linarith only [hlam, p11934_0]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        rcases p11934_3 (m.d 0 3) (by simp) with h11936 | h11936
                                        · rcases p11934_3 (m.d 1 3) (by simp) with h11937 | h11937
                                          · linarith only [h1, h11937, hlam]
                                          · rcases p11934_3 (m.d 2 3) (by simp) with h11939 | h11939
                                            · rcases p11934_3 (m.d 3 4) (by simp) with h11940 | h11940
                                              · linarith only [h11940, h9965, hlam]
                                              · rcases p11934_3 (m.d 3 5) (by simp) with h11942 | h11942
                                                · linarith only [h11942, h9966, hlam]
                                                · rcases h5bigk with h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c | h11944c
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [hlam, p11944_0]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h11675, h11681, h9029, hc12, hc25, hlam, hphi, p11944_1]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h9029, hlam, p11944_0]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h11686, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11688_1, p11944_1]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h9967, hlam, p11944_1]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h3, hlam, p11944_0]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [hlam, p11944_0]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h11677, hlam, p11944_0]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h11686, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11944_1]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h11681, hlam, p11944_1]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h0, h9029, hc12, hc25, hlam, hphi, p11944_1]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h11677, hc12, hc25, hlam, hphi, p11944_1]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [hlam, p11944_0]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    rcases p11944_3 (m.d 0 5) (by simp) with h11958 | h11958
                                                    · linarith only [h11958, h9029, hlam]
                                                    · linarith only [h11958, h9966, hlam]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h11675, h11683, h11685, h2, h9967, hc12, hc23, hlam, hphi, p11944_1]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h9966, hlam, p11944_0]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h11680, hlam, p11944_0]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h11684, hlam, p11944_0]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [hlam, p11944_0]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h11686, hlam, p11944_1]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h11675, h2, h9967, hc12, hc45, hlam, hphi, ht23, ht34, p11944_1]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h11675, h11680, h11681, h11686, h4, hc12, hc23, hc34, hc45, hlam, hphi, p11934_1, p11944_1]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h11685, hlam, p11944_0]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [h11683, h11685, h11686, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11944_1]
                                                  · have p11944_0 := h11944c.1
                                                    have p11944_1 := h11944c.2.1
                                                    have p11944_2 := h11944c.2.2.1
                                                    have p11944_3 := h11944c.2.2.2
                                                    linarith only [hlam, p11944_0]
                                            · linarith only [h11673, h11939, hlam]
                                        · linarith only [h1, h11936, hlam]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        linarith only [h4, hlam, p11934_1]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        rcases p11934_3 (m.d 0 3) (by simp) with h11975 | h11975
                                        · rcases p11934_3 (m.d 1 3) (by simp) with h11976 | h11976
                                          · linarith only [h1, h11976, hlam]
                                          · linarith only [h11679, h11976, hlam]
                                        · linarith only [h11975, hlam, p11934_0]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        rcases p11934_3 (m.d 0 3) (by simp) with h11980 | h11980
                                        · rcases p11934_3 (m.d 1 3) (by simp) with h11981 | h11981
                                          · linarith only [h1, h11981, hlam]
                                          · linarith only [h11680, h11981, hlam]
                                        · linarith only [h11980, hlam, p11934_0]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        linarith only [h1, hlam, p11934_0]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        linarith only [hlam, p11934_0]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        linarith only [h11673, hlam, p11934_1]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        rcases p11934_3 (m.d 0 3) (by simp) with h11988 | h11988
                                        · rcases p11934_3 (m.d 1 3) (by simp) with h11989 | h11989
                                          · rcases p11934_3 (m.d 2 3) (by simp) with h11990 | h11990
                                            · rcases p11934_3 (m.d 3 4) (by simp) with h11991 | h11991
                                              · linarith only [h11991, hlam, p11934_0]
                                              · rcases p11934_3 (m.d 3 5) (by simp) with h11993 | h11993
                                                · linarith only [h11680, h11993, hlam]
                                                · linarith only [h11686, h11993, hlam]
                                            · linarith only [h11683, h11990, hlam]
                                          · linarith only [h11989, hlam, p11934_0]
                                        · linarith only [h11988, h9965, hlam]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        rcases p11934_3 (m.d 0 3) (by simp) with h11999 | h11999
                                        · rcases p11934_3 (m.d 1 3) (by simp) with h12000 | h12000
                                          · rcases p11934_3 (m.d 2 3) (by simp) with h12001 | h12001
                                            · rcases p11934_3 (m.d 3 4) (by simp) with h12002 | h12002
                                              · linarith only [h11679, h12002, hlam]
                                              · rcases p11934_3 (m.d 3 5) (by simp) with h12004 | h12004
                                                · linarith only [h12004, hlam, p11934_0]
                                                · rcases h5bigk with h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c | h12006c
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [hlam, p12006_0]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h11675, h11681, h11683, h11685, h9029, hc12, hc23, hlam, hphi, p12006_1]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h9029, hlam, p12006_0]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h11686, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11688_1, p12006_1]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h9967, hlam, p12006_1]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h3, hlam, p12006_0]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [hlam, p12006_0]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h11677, hlam, p12006_0]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h11686, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12006_1]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h11681, hlam, p12006_1]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h0, h11683, h11685, h9029, hc12, hc23, hlam, hphi, p12006_1]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h11677, h11683, h11685, hc12, hc23, hlam, hphi, p12006_1]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [hlam, p12006_0]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    rcases p12006_3 (m.d 0 5) (by simp) with h12020 | h12020
                                                    · linarith only [h12020, h9029, hlam]
                                                    · linarith only [h12020, h9966, hlam]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h11675, h11683, h11685, h2, h9967, hc12, hc23, hlam, hphi, p12006_1]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h9966, hlam, p12006_0]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h11680, hlam, p12006_0]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h11684, hlam, p12006_0]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [hlam, p12006_0]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h11686, hlam, p12006_1]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h11675, h2, h9967, hc12, hc45, hlam, hphi, ht23, ht34, p12006_1]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h11675, h11681, hc12, hc45, hlam, hphi, ht23, ht34, p12006_1]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h11685, hlam, p12006_0]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [h11683, h11685, h11686, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12006_1]
                                                  · have p12006_0 := h12006c.1
                                                    have p12006_1 := h12006c.2.1
                                                    have p12006_2 := h12006c.2.2.1
                                                    have p12006_3 := h12006c.2.2.2
                                                    linarith only [hlam, p12006_0]
                                            · linarith only [h11684, h12001, hlam]
                                          · linarith only [h12000, hlam, p11934_0]
                                        · linarith only [h11999, h9966, hlam]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        linarith only [h11675, h2, h9967, hc12, hc23, hlam, hphi, p11688_1, p11934_1]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        rcases p11934_3 (m.d 0 3) (by simp) with h12038 | h12038
                                        · linarith only [h12038, h4, hlam]
                                        · linarith only [h1, h12038, hlam]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        linarith only [hlam, p11934_0]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        rcases p11934_3 (m.d 0 3) (by simp) with h12042 | h12042
                                        · linarith only [h12042, h4, hlam]
                                        · linarith only [h12042, h9965, hlam]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        rcases p11934_3 (m.d 0 3) (by simp) with h12045 | h12045
                                        · linarith only [h12045, h4, hlam]
                                        · linarith only [h12045, h9966, hlam]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        linarith only [h9965, hlam, p11934_0]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        linarith only [h11679, hlam, p11934_0]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        linarith only [h11683, hlam, p11934_0]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        linarith only [hlam, p11934_0]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        linarith only [h11686, hlam, p11934_1]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        linarith only [h9966, hlam, p11934_0]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        linarith only [h11680, hlam, p11934_0]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        linarith only [h11684, hlam, p11934_0]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        linarith only [h1, h11680, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11934_1]
                                      · have p11934_0 := h11934c.1
                                        have p11934_1 := h11934c.2.1
                                        have p11934_2 := h11934c.2.2.1
                                        have p11934_3 := h11934c.2.2.2
                                        linarith only [hlam, p11934_0]
                                    · linarith only [h11933, hlam, p11884_0]
                                  · linarith only [h11932, h7821, hlam]
                                · linarith only [h11931, h4, hlam]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            rcases p11884_3 (m.d 0 2) (by simp) with h12061 | h12061
                            · linarith only [h12061, h9029, hlam]
                            · linarith only [h0, h12061, hlam]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [h11684, hlam, p11884_1]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [h11685, hlam, p11884_0]
                          · have p11884_0 := h11884c.1
                            have p11884_1 := h11884c.2.1
                            have p11884_2 := h11884c.2.2.1
                            have p11884_3 := h11884c.2.2.2
                            linarith only [hlam, p11884_0]
                    · linarith only [h11879, h9966, hlam]
                · linarith only [h11876, h3, hlam]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [h2, hlam, p11688_0]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [h0, h11683, h11685, h9967, hc12, hc23, hlam, hphi, p11688_1]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [h9965, hlam, p11688_0]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [hlam, p11688_0]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [h9967, hlam, p11688_0]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [h3, hlam, p11688_0]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [h0, h11683, h11685, h9967, hc12, hc23, hlam, hphi, p11688_1]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [h9966, hlam, p11688_0]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [h11675, h11683, h11685, h2, h9967, hc12, hc23, hlam, hphi, p11688_1]
              · have p11688_0 := h11688c.1
                have p11688_1 := h11688c.2.1
                have p11688_2 := h11688c.2.2.1
                have p11688_3 := h11688c.2.2.2
                linarith only [hlam, p11688_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h12079 | h12079
            · linarith only [h0, h11685, h12079, h7821, hc12, hc34, hlam, hphi, ht23]
            · rcases h0bigk with h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c | h12081c
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                linarith only [hlam, p12081_0]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                rcases p12081_3 (m.d 0 1) (by simp) with h12083 | h12083
                · rcases p12081_3 (m.d 0 2) (by simp) with h12084 | h12084
                  · linarith only [h0, h12084, hlam]
                  · rcases p12081_3 (m.d 0 3) (by simp) with h12086 | h12086
                    · linarith only [h1, h12086, hlam]
                    · linarith only [h12086, h4, hlam]
                · linarith only [h0, h12083, hlam]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                rcases p12081_3 (m.d 0 1) (by simp) with h12090 | h12090
                · rcases p12081_3 (m.d 0 2) (by simp) with h12091 | h12091
                  · linarith only [h0, h12091, hlam]
                  · rcases p12081_3 (m.d 0 3) (by simp) with h12093 | h12093
                    · linarith only [h1, h12093, hlam]
                    · rcases p12081_3 (m.d 0 4) (by simp) with h12095 | h12095
                      · linarith only [h12095, h2, hlam]
                      · rcases p12081_3 (m.d 0 5) (by simp) with h12097 | h12097
                        · linarith only [h12097, h3, hlam]
                        · rcases h2bigk with h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c | h12099c
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [hlam, p12099_0]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [h7821, hc12, hc24, hlam, hphi, p12099_1]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [h4, hlam, p12099_0]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [h7821, hlam, p12099_0]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [h9029, hlam, p12099_0]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [h0, hlam, p12099_0]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [hlam, p12099_0]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [h11673, hlam, p12099_0]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [h11675, hlam, p12099_0]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [h11677, hlam, p12099_0]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            rcases p12099_3 (m.d 0 2) (by simp) with h12110 | h12110
                            · linarith only [h12110, hlam, p12099_0]
                            · rcases p12099_3 (m.d 1 2) (by simp) with h12112 | h12112
                              · linarith only [h11673, h12112, hlam]
                              · rcases p12099_3 (m.d 2 3) (by simp) with h12114 | h12114
                                · rcases p12099_3 (m.d 2 4) (by simp) with h12115 | h12115
                                  · linarith only [h11683, h12115, hlam]
                                  · linarith only [h12115, h7821, hlam]
                                · linarith only [h12114, hlam, p12099_0]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            rcases p12099_3 (m.d 0 2) (by simp) with h12119 | h12119
                            · linarith only [h12119, h4, hlam]
                            · linarith only [h0, h12119, hlam]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [hlam, p12099_0]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [h7821, hc02, hc23, hlam, hphi, p12099_1]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [h0, h9029, hc12, hc23, hlam, hphi, p12099_1]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [h0, h11685, hc12, hc45, hlam, hphi, ht23, ht34, p12099_1]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [h11685, hc12, hc45, hlam, hphi, ht23, ht34, p12099_1]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [h11683, hlam, p12099_1]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [hlam, p12099_0]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [h11685, hlam, p12099_1]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            rcases p12099_3 (m.d 0 2) (by simp) with h12130 | h12130
                            · linarith only [h12130, hlam, p12099_0]
                            · rcases p12099_3 (m.d 1 2) (by simp) with h12132 | h12132
                              · linarith only [h11677, h12132, hlam]
                              · rcases p12099_3 (m.d 2 3) (by simp) with h12134 | h12134
                                · rcases p12099_3 (m.d 2 4) (by simp) with h12135 | h12135
                                  · linarith only [h11685, h12135, hlam]
                                  · linarith only [h12135, h7821, hlam]
                                · linarith only [h12134, h4, hlam]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            rcases p12099_3 (m.d 0 2) (by simp) with h12139 | h12139
                            · linarith only [h12139, h9029, hlam]
                            · linarith only [h0, h12139, hlam]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [h11684, hlam, p12099_1]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [h0, h7821, hc12, hc25, hlam, hphi, p12099_1]
                          · have p12099_0 := h12099c.1
                            have p12099_1 := h12099c.2.1
                            have p12099_2 := h12099c.2.2.1
                            have p12099_3 := h12099c.2.2.2
                            linarith only [hlam, p12099_0]
                · linarith only [h1, h12090, hlam]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                rcases p12081_3 (m.d 0 1) (by simp) with h12146 | h12146
                · rcases p12081_3 (m.d 0 2) (by simp) with h12147 | h12147
                  · linarith only [h0, h12147, hlam]
                  · rcases p12081_3 (m.d 0 3) (by simp) with h12149 | h12149
                    · linarith only [h1, h12149, hlam]
                    · linarith only [h12149, h9965, hlam]
                · linarith only [h12146, h2, hlam]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                rcases p12081_3 (m.d 0 1) (by simp) with h12153 | h12153
                · rcases p12081_3 (m.d 0 2) (by simp) with h12154 | h12154
                  · linarith only [h0, h12154, hlam]
                  · rcases p12081_3 (m.d 0 3) (by simp) with h12156 | h12156
                    · linarith only [h1, h12156, hlam]
                    · linarith only [h12156, h9966, hlam]
                · linarith only [h12153, h3, hlam]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                linarith only [h0, hlam, p12081_0]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                linarith only [hlam, p12081_0]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                linarith only [h4, hlam, p12081_0]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                linarith only [h7821, hlam, p12081_1]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                linarith only [h9029, hlam, p12081_0]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                linarith only [h1, hlam, p12081_1]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                rcases p12081_3 (m.d 0 1) (by simp) with h12166 | h12166
                · rcases p12081_3 (m.d 0 2) (by simp) with h12167 | h12167
                  · linarith only [h12167, h4, hlam]
                  · rcases p12081_3 (m.d 0 3) (by simp) with h12169 | h12169
                    · rcases p12081_3 (m.d 0 4) (by simp) with h12170 | h12170
                      · linarith only [h12170, h9965, hlam]
                      · linarith only [h12170, h7821, hlam]
                    · linarith only [h12169, h4, hlam]
                · linarith only [h0, h12166, hlam]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                linarith only [hlam, p12081_0]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                rcases p12081_3 (m.d 0 1) (by simp) with h12176 | h12176
                · rcases p12081_3 (m.d 0 2) (by simp) with h12177 | h12177
                  · linarith only [h12177, h4, hlam]
                  · rcases p12081_3 (m.d 0 3) (by simp) with h12179 | h12179
                    · rcases p12081_3 (m.d 0 4) (by simp) with h12180 | h12180
                      · linarith only [h12180, h9965, hlam]
                      · rcases p12081_3 (m.d 0 5) (by simp) with h12182 | h12182
                        · linarith only [h12182, h9966, hlam]
                        · linarith only [h12182, h9967, hlam]
                    · linarith only [h12179, h9965, hlam]
                · linarith only [h12176, h2, hlam]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                rcases p12081_3 (m.d 0 1) (by simp) with h12187 | h12187
                · rcases p12081_3 (m.d 0 2) (by simp) with h12188 | h12188
                  · linarith only [h12188, h4, hlam]
                  · rcases p12081_3 (m.d 0 3) (by simp) with h12190 | h12190
                    · rcases p12081_3 (m.d 0 4) (by simp) with h12191 | h12191
                      · linarith only [h12191, h9965, hlam]
                      · rcases p12081_3 (m.d 0 5) (by simp) with h12193 | h12193
                        · linarith only [h12193, h9966, hlam]
                        · rcases h2bigk with h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c | h12195c
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [hlam, p12195_0]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p12195_1]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [h4, hlam, p12195_0]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [h7821, hlam, p12195_0]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [h9029, hlam, p12195_0]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [h0, hlam, p12195_0]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [hlam, p12195_0]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [h11673, hlam, p12195_0]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [h11675, hlam, p12195_0]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [h11677, hlam, p12195_0]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            rcases p12195_3 (m.d 0 2) (by simp) with h12206 | h12206
                            · linarith only [h12206, hlam, p12195_0]
                            · rcases p12195_3 (m.d 1 2) (by simp) with h12208 | h12208
                              · linarith only [h11673, h12208, hlam]
                              · rcases p12195_3 (m.d 2 3) (by simp) with h12210 | h12210
                                · rcases p12195_3 (m.d 2 4) (by simp) with h12211 | h12211
                                  · linarith only [h11683, h12211, hlam]
                                  · linarith only [h12211, h7821, hlam]
                                · linarith only [h12210, hlam, p12195_0]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            rcases p12195_3 (m.d 0 2) (by simp) with h12215 | h12215
                            · linarith only [h12215, h4, hlam]
                            · linarith only [h0, h12215, hlam]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [hlam, p12195_0]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [h7821, hc02, hc23, hlam, hphi, p12195_1]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [h0, h9029, hc12, hc23, hlam, hphi, p12195_1]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [h0, h11685, hc12, hc45, hlam, hphi, ht23, ht34, p12195_1]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [h11685, hc12, hc45, hlam, hphi, ht23, ht34, p12195_1]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [h11683, hlam, p12195_1]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [hlam, p12195_0]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [h11685, hlam, p12195_1]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            rcases p12195_3 (m.d 0 2) (by simp) with h12226 | h12226
                            · linarith only [h12226, hlam, p12195_0]
                            · rcases p12195_3 (m.d 1 2) (by simp) with h12228 | h12228
                              · linarith only [h11677, h12228, hlam]
                              · rcases p12195_3 (m.d 2 3) (by simp) with h12230 | h12230
                                · rcases p12195_3 (m.d 2 4) (by simp) with h12231 | h12231
                                  · linarith only [h11685, h12231, hlam]
                                  · linarith only [h12231, h7821, hlam]
                                · linarith only [h12230, h4, hlam]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            rcases p12195_3 (m.d 0 2) (by simp) with h12235 | h12235
                            · linarith only [h12235, h9029, hlam]
                            · linarith only [h0, h12235, hlam]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [h11684, hlam, p12195_1]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [h0, h7821, hc12, hc25, hlam, hphi, p12195_1]
                          · have p12195_0 := h12195c.1
                            have p12195_1 := h12195c.2.1
                            have p12195_2 := h12195c.2.2.1
                            have p12195_3 := h12195c.2.2.2
                            linarith only [hlam, p12195_0]
                    · linarith only [h12190, h9966, hlam]
                · linarith only [h12187, h3, hlam]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                linarith only [h2, hlam, p12081_0]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                linarith only [h0, h9967, hc12, hc45, hlam, hphi, ht23, ht34, p12081_1]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                linarith only [h9965, hlam, p12081_0]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                linarith only [hlam, p12081_0]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                linarith only [h9967, hlam, p12081_0]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                linarith only [h3, hlam, p12081_0]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                rcases p12081_3 (m.d 0 1) (by simp) with h12249 | h12249
                · rcases p12081_3 (m.d 0 2) (by simp) with h12250 | h12250
                  · linarith only [h12250, h9029, hlam]
                  · rcases p12081_3 (m.d 0 3) (by simp) with h12252 | h12252
                    · rcases p12081_3 (m.d 0 4) (by simp) with h12253 | h12253
                      · linarith only [h12253, h9967, hlam]
                      · linarith only [h12253, h7821, hlam]
                    · linarith only [h12252, h4, hlam]
                · linarith only [h0, h12249, hlam]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                linarith only [h9966, hlam, p12081_0]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                rcases p12081_3 (m.d 0 1) (by simp) with h12259 | h12259
                · rcases p12081_3 (m.d 0 2) (by simp) with h12260 | h12260
                  · linarith only [h12260, h9029, hlam]
                  · rcases p12081_3 (m.d 0 3) (by simp) with h12262 | h12262
                    · rcases p12081_3 (m.d 0 4) (by simp) with h12263 | h12263
                      · linarith only [h12263, h9967, hlam]
                      · rcases p12081_3 (m.d 0 5) (by simp) with h12265 | h12265
                        · rcases h2bigk with h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c | h12266c
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [hlam, p12266_0]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p12266_1]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [h4, hlam, p12266_0]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [h7821, hlam, p12266_0]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [h9029, hlam, p12266_0]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [h0, hlam, p12266_0]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [hlam, p12266_0]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [h11673, hlam, p12266_0]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [h11675, hlam, p12266_0]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [h11677, hlam, p12266_0]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            rcases p12266_3 (m.d 0 2) (by simp) with h12277 | h12277
                            · linarith only [h12277, hlam, p12266_0]
                            · rcases p12266_3 (m.d 1 2) (by simp) with h12279 | h12279
                              · linarith only [h11673, h12279, hlam]
                              · rcases p12266_3 (m.d 2 3) (by simp) with h12281 | h12281
                                · rcases p12266_3 (m.d 2 4) (by simp) with h12282 | h12282
                                  · linarith only [h11683, h12282, hlam]
                                  · linarith only [h12282, h7821, hlam]
                                · linarith only [h12281, hlam, p12266_0]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            rcases p12266_3 (m.d 0 2) (by simp) with h12286 | h12286
                            · linarith only [h12286, h4, hlam]
                            · linarith only [h0, h12286, hlam]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [hlam, p12266_0]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [h7821, hc02, hc23, hlam, hphi, p12266_1]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [h0, h9029, hc12, hc23, hlam, hphi, p12266_1]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [h0, h11685, hc12, hc45, hlam, hphi, ht23, ht34, p12266_1]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [h11685, hc12, hc45, hlam, hphi, ht23, ht34, p12266_1]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [h11683, hlam, p12266_1]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [hlam, p12266_0]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [h11685, hlam, p12266_1]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            rcases p12266_3 (m.d 0 2) (by simp) with h12297 | h12297
                            · linarith only [h12297, hlam, p12266_0]
                            · rcases p12266_3 (m.d 1 2) (by simp) with h12299 | h12299
                              · linarith only [h11677, h12299, hlam]
                              · rcases p12266_3 (m.d 2 3) (by simp) with h12301 | h12301
                                · rcases p12266_3 (m.d 2 4) (by simp) with h12302 | h12302
                                  · linarith only [h11685, h12302, hlam]
                                  · linarith only [h12302, h7821, hlam]
                                · linarith only [h12301, h4, hlam]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            rcases p12266_3 (m.d 0 2) (by simp) with h12306 | h12306
                            · linarith only [h12306, h9029, hlam]
                            · linarith only [h0, h12306, hlam]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [h11684, hlam, p12266_1]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [h0, h7821, hc12, hc25, hlam, hphi, p12266_1]
                          · have p12266_0 := h12266c.1
                            have p12266_1 := h12266c.2.1
                            have p12266_2 := h12266c.2.2.1
                            have p12266_3 := h12266c.2.2.2
                            linarith only [hlam, p12266_0]
                        · linarith only [h12265, h9967, hlam]
                    · linarith only [h12262, h9965, hlam]
                · linarith only [h12259, h2, hlam]
              · have p12081_0 := h12081c.1
                have p12081_1 := h12081c.2.1
                have p12081_2 := h12081c.2.2.1
                have p12081_3 := h12081c.2.2.2
                linarith only [hlam, p12081_0]
        · linarith only [h11684, h4, h9966, hlam]
      · linarith only [h11683, h4, h9965, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h12318 | h12318
    · linarith only [h11679, h11680, h12318, h7821, h9966, h9967, hc02, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h12320 | h12320
      · rcases m.htr 2 3 5 (by decide) (by decide) with h12321 | h12321
        · rcases m.htr 2 4 5 (by decide) (by decide) with h12322 | h12322
          · rcases m.htr 3 4 5 (by decide) (by decide) with h12323 | h12323
            · linarith only [h11679, h11680, h12323, h9966, h9967, hlam]
            · rcases h0bigk with h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c | h12325c
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [hlam, p12325_0]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                rcases p12325_3 (m.d 0 1) (by simp) with h12327 | h12327
                · rcases p12325_3 (m.d 0 2) (by simp) with h12328 | h12328
                  · linarith only [h0, h12328, hlam]
                  · rcases p12325_3 (m.d 0 3) (by simp) with h12330 | h12330
                    · linarith only [h1, h12330, hlam]
                    · linarith only [h12330, h4, hlam]
                · linarith only [h0, h12327, hlam]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [h11679, h11680, h9966, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12325_1]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                rcases p12325_3 (m.d 0 1) (by simp) with h12335 | h12335
                · rcases p12325_3 (m.d 0 2) (by simp) with h12336 | h12336
                  · linarith only [h0, h12336, hlam]
                  · rcases p12325_3 (m.d 0 3) (by simp) with h12338 | h12338
                    · linarith only [h1, h12338, hlam]
                    · linarith only [h12338, h9965, hlam]
                · linarith only [h12335, h2, hlam]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [h11679, h11680, h9966, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12325_1]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [h0, hlam, p12325_0]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [hlam, p12325_0]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [h4, hlam, p12325_0]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [h7821, hlam, p12325_1]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [h9029, hlam, p12325_0]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [h1, hlam, p12325_1]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                rcases p12325_3 (m.d 0 1) (by simp) with h12349 | h12349
                · rcases p12325_3 (m.d 0 2) (by simp) with h12350 | h12350
                  · linarith only [h12350, h4, hlam]
                  · rcases p12325_3 (m.d 0 3) (by simp) with h12352 | h12352
                    · rcases p12325_3 (m.d 0 4) (by simp) with h12353 | h12353
                      · linarith only [h12353, h9965, hlam]
                      · linarith only [h12353, h7821, hlam]
                    · linarith only [h12352, h4, hlam]
                · linarith only [h0, h12349, hlam]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [hlam, p12325_0]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                rcases p12325_3 (m.d 0 1) (by simp) with h12359 | h12359
                · rcases p12325_3 (m.d 0 2) (by simp) with h12360 | h12360
                  · linarith only [h12360, h4, hlam]
                  · rcases p12325_3 (m.d 0 3) (by simp) with h12362 | h12362
                    · rcases p12325_3 (m.d 0 4) (by simp) with h12363 | h12363
                      · linarith only [h12363, h9965, hlam]
                      · rcases p12325_3 (m.d 0 5) (by simp) with h12365 | h12365
                        · linarith only [h12365, h9966, hlam]
                        · linarith only [h12365, h9967, hlam]
                    · linarith only [h12362, h9965, hlam]
                · linarith only [h12359, h2, hlam]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [h11679, h11680, h9966, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p12325_1]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [h2, hlam, p12325_0]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [h9967, hc02, hc45, hlam, hphi, ht23, ht34, p12325_1]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [h9965, hlam, p12325_0]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [hlam, p12325_0]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [h9967, hlam, p12325_0]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [h3, hlam, p12325_0]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [h12320, h12322, h9967, hc02, hc23, hlam, hphi, p12325_1]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [h9966, hlam, p12325_0]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [h0, h12320, h12322, h7821, h9967, hc12, hc23, hlam, hphi, p12325_1]
              · have p12325_0 := h12325c.1
                have p12325_1 := h12325c.2.1
                have p12325_2 := h12325c.2.2.1
                have p12325_3 := h12325c.2.2.2
                linarith only [hlam, p12325_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h12381 | h12381
            · linarith only [h11679, h11680, h12322, h12381, h9966, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases h0bigk with h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c | h12383c
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [hlam, p12383_0]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                rcases p12383_3 (m.d 0 1) (by simp) with h12385 | h12385
                · rcases p12383_3 (m.d 0 2) (by simp) with h12386 | h12386
                  · linarith only [h0, h12386, hlam]
                  · rcases p12383_3 (m.d 0 3) (by simp) with h12388 | h12388
                    · linarith only [h1, h12388, hlam]
                    · linarith only [h12388, h4, hlam]
                · linarith only [h0, h12385, hlam]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [h11680, h9966, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p12383_1]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                rcases p12383_3 (m.d 0 1) (by simp) with h12393 | h12393
                · rcases p12383_3 (m.d 0 2) (by simp) with h12394 | h12394
                  · linarith only [h0, h12394, hlam]
                  · rcases p12383_3 (m.d 0 3) (by simp) with h12396 | h12396
                    · linarith only [h1, h12396, hlam]
                    · linarith only [h12396, h9965, hlam]
                · linarith only [h12393, h2, hlam]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [h11679, h11680, h9966, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12383_1]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [h0, hlam, p12383_0]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [hlam, p12383_0]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [h4, hlam, p12383_0]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [h7821, hlam, p12383_1]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [h9029, hlam, p12383_0]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [h1, hlam, p12383_1]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                rcases p12383_3 (m.d 0 1) (by simp) with h12407 | h12407
                · rcases p12383_3 (m.d 0 2) (by simp) with h12408 | h12408
                  · linarith only [h12408, h4, hlam]
                  · rcases p12383_3 (m.d 0 3) (by simp) with h12410 | h12410
                    · rcases p12383_3 (m.d 0 4) (by simp) with h12411 | h12411
                      · linarith only [h12411, h9965, hlam]
                      · linarith only [h12411, h7821, hlam]
                    · linarith only [h12410, h4, hlam]
                · linarith only [h0, h12407, hlam]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [hlam, p12383_0]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                rcases p12383_3 (m.d 0 1) (by simp) with h12417 | h12417
                · rcases p12383_3 (m.d 0 2) (by simp) with h12418 | h12418
                  · linarith only [h12418, h4, hlam]
                  · rcases p12383_3 (m.d 0 3) (by simp) with h12420 | h12420
                    · rcases p12383_3 (m.d 0 4) (by simp) with h12421 | h12421
                      · linarith only [h12421, h9965, hlam]
                      · rcases p12383_3 (m.d 0 5) (by simp) with h12423 | h12423
                        · linarith only [h12423, h9966, hlam]
                        · linarith only [h12423, h9967, hlam]
                    · linarith only [h12420, h9965, hlam]
                · linarith only [h12417, h2, hlam]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [h11679, h11680, h9966, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p12383_1]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [h2, hlam, p12383_0]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [h0, h12322, h7821, hc12, hc45, hlam, hphi, ht23, ht34, p12383_1]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [h9965, hlam, p12383_0]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [hlam, p12383_0]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [h9967, hlam, p12383_0]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [h3, hlam, p12383_0]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                rcases p12383_3 (m.d 0 1) (by simp) with h12435 | h12435
                · rcases p12383_3 (m.d 0 2) (by simp) with h12436 | h12436
                  · linarith only [h12436, h9029, hlam]
                  · rcases p12383_3 (m.d 0 3) (by simp) with h12438 | h12438
                    · rcases p12383_3 (m.d 0 4) (by simp) with h12439 | h12439
                      · linarith only [h12439, h9967, hlam]
                      · linarith only [h12439, h7821, hlam]
                    · linarith only [h12438, h4, hlam]
                · linarith only [h0, h12435, hlam]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [h9966, hlam, p12383_0]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                rcases p12383_3 (m.d 0 1) (by simp) with h12445 | h12445
                · rcases p12383_3 (m.d 0 2) (by simp) with h12446 | h12446
                  · linarith only [h12446, h9029, hlam]
                  · rcases p12383_3 (m.d 0 3) (by simp) with h12448 | h12448
                    · rcases p12383_3 (m.d 0 4) (by simp) with h12449 | h12449
                      · linarith only [h12449, h9967, hlam]
                      · rcases p12383_3 (m.d 0 5) (by simp) with h12451 | h12451
                        · rcases h2bigk with h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c | h12452c
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [hlam, p12452_0]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p12452_1]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [h4, hlam, p12452_0]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [h7821, hlam, p12452_0]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [h9029, hlam, p12452_0]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [h0, hlam, p12452_0]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [hlam, p12452_0]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [h11673, hlam, p12452_0]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [h11675, hlam, p12452_0]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [h11677, hlam, p12452_0]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            rcases p12452_3 (m.d 0 2) (by simp) with h12463 | h12463
                            · linarith only [h12463, hlam, p12452_0]
                            · rcases p12452_3 (m.d 1 2) (by simp) with h12465 | h12465
                              · linarith only [h11673, h12465, hlam]
                              · rcases p12452_3 (m.d 2 3) (by simp) with h12467 | h12467
                                · rcases p12452_3 (m.d 2 4) (by simp) with h12468 | h12468
                                  · linarith only [h12320, h12468, hlam]
                                  · linarith only [h12468, h7821, hlam]
                                · linarith only [h12467, hlam, p12452_0]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            rcases p12452_3 (m.d 0 2) (by simp) with h12472 | h12472
                            · linarith only [h12472, h4, hlam]
                            · linarith only [h0, h12472, hlam]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [hlam, p12452_0]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [h7821, hc02, hc23, hlam, hphi, p12452_1]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [h9029, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12383_1, p12452_1]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [h0, h12322, hc12, hc45, hlam, hphi, ht23, ht34, p12452_1]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [h12322, hc12, hc45, hlam, hphi, ht23, ht34, p12452_1]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [h12320, hlam, p12452_1]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [hlam, p12452_0]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [h12322, hlam, p12452_1]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            rcases p12452_3 (m.d 0 2) (by simp) with h12483 | h12483
                            · linarith only [h12483, hlam, p12452_0]
                            · rcases p12452_3 (m.d 1 2) (by simp) with h12485 | h12485
                              · linarith only [h11677, h12485, hlam]
                              · rcases p12452_3 (m.d 2 3) (by simp) with h12487 | h12487
                                · rcases p12452_3 (m.d 2 4) (by simp) with h12488 | h12488
                                  · linarith only [h12322, h12488, hlam]
                                  · linarith only [h12488, h7821, hlam]
                                · linarith only [h12487, h4, hlam]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            rcases p12452_3 (m.d 0 2) (by simp) with h12492 | h12492
                            · linarith only [h12492, h9029, hlam]
                            · linarith only [h0, h12492, hlam]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [h12321, hlam, p12452_1]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [h0, h7821, hc12, hc25, hlam, hphi, p12452_1]
                          · have p12452_0 := h12452c.1
                            have p12452_1 := h12452c.2.1
                            have p12452_2 := h12452c.2.2.1
                            have p12452_3 := h12452c.2.2.2
                            linarith only [hlam, p12452_0]
                        · linarith only [h12451, h9967, hlam]
                    · linarith only [h12448, h9965, hlam]
                · linarith only [h12445, h2, hlam]
              · have p12383_0 := h12383c.1
                have p12383_1 := h12383c.2.1
                have p12383_2 := h12383c.2.2.1
                have p12383_3 := h12383c.2.2.2
                linarith only [hlam, p12383_0]
        · linarith only [h12321, h4, h9966, hlam]
      · linarith only [h11679, h11680, h12320, h4, h9966, hlam]

end R2N4
