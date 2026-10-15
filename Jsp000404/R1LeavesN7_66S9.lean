import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_66S8

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_H_I_L_0_L_0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h2elo := hb2.1
  have h4elo := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h672 | h672
  · rcases m.htr 0 1 4 (by decide) (by decide) with h673 | h673
    · rcases m.htr 0 2 3 (by decide) (by decide) with h674 | h674
      · rcases m.htr 0 2 4 (by decide) (by decide) with h675 | h675
        · rcases m.htr 0 2 5 (by decide) (by decide) with h676 | h676
          · rcases m.htr 0 3 4 (by decide) (by decide) with h677 | h677
            · rcases m.htr 0 3 5 (by decide) (by decide) with h678 | h678
              · rcases m.htr 0 4 5 (by decide) (by decide) with h679 | h679
                · rcases m.htr 1 2 3 (by decide) (by decide) with h680 | h680
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h681 | h681
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h682 | h682
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h683 | h683
                        · linarith only [h0, h672, h680, h683, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h0, h672, h677, h683, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h672, h676, h682, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h672, h680, h681, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h680, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h689 | h689
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h690 | h690
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h691 | h691
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h692 | h692
                        · linarith only [h0, h672, h689, h692, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h0, h672, h677, h692, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h672, h676, h678, h691, hlam]
                    · linarith only [h0, h690, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h672, h689, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h698 | h698
                · linarith only [h677, h678, h698, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h700 | h700
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h701 | h701
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h702 | h702
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h703 | h703
                        · linarith only [h0, h672, h700, h703, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h677, h678, h703, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h702, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h672, h700, h701, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h700, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h709 | h709
              · rcases m.htr 0 4 5 (by decide) (by decide) with h710 | h710
                · rcases m.htr 1 2 3 (by decide) (by decide) with h711 | h711
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h712 | h712
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h713 | h713
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h714 | h714
                        · linarith only [h0, h672, h677, h711, h714, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h716 | h716
                          · linarith only [h0, h673, h712, h714, h716, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h677, h709, h716, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h672, h676, h677, h709, h711, h713, hc23, hlam, hphi, ht34, u4elo3]
                    · linarith only [h0, h672, h711, h712, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h711, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h677, h709, h710, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h723 | h723
                · rcases m.htr 1 2 3 (by decide) (by decide) with h724 | h724
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h725 | h725
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h726 | h726
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h727 | h727
                        · linarith only [h0, h672, h724, h727, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h729 | h729
                          · linarith only [h0, h673, h725, h727, h729, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h731 | h731
                            · linarith only [h0, h673, h725, h731, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h0, h673, h723, h727, h731, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h726, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h725, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h672, h724, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h737 | h737
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h738 | h738
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h739 | h739
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h740 | h740
                        · linarith only [h0, h672, h737, h740, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h742 | h742
                          · linarith only [h0, h673, h709, h738, h740, h742, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h744 | h744
                            · linarith only [h0, h673, h738, h744, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases h0bigk with h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [hlam, p746_0]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h0, hlam, p746_1]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h0, h672, h737, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p746_1, u2elo1]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p746_1, u2elo1]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p746_1, u2elo1]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p746_1, u2elo1]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [hlam, p746_0]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h0, h672, h737, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p746_1, u2elo1]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h0, h673, h738, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p746_1, u2elo1]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h0, h676, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p746_1, u2elo1]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h672, hlam, p746_1]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h674, hlam, p746_1]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [hlam, p746_0]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h677, hlam, p746_1]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h709, hlam, p746_1]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h673, hlam, p746_0]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h675, hlam, p746_0]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h672, h723, h737, hc23, hlam, hphi, ht34, p746_1, u4elo4]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [hlam, p746_0]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h723, hlam, p746_0]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h673, h738, h740, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p746_1]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h676, hlam, p746_1]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h0, h672, h676, h737, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p746_1, u2elo1]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [h723, hc04, hlam, hphi, p746_1, u4elo4]
                              · have p746_0 := h746c.1
                                have p746_1 := h746c.2.1
                                have p746_2 := h746c.2.2.1
                                have p746_3 := h746c.2.2.2
                                linarith only [hlam, p746_0]
                      · linarith only [h0, h739, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h672, h737, h738, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h672, h737, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h775 | h775
            · rcases m.htr 0 3 5 (by decide) (by decide) with h776 | h776
              · linarith only [h0, h672, h676, h776, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h778 | h778
                · linarith only [h0, h672, h676, h775, h778, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h780 | h780
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h781 | h781
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h782 | h782
                      · linarith only [h0, h676, h782, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h672, h780, h782, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h672, h780, h781, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h780, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h787 | h787
              · linarith only [h0, h672, h676, h775, h787, hc13, hlam, hphi, ht34, u4elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h789 | h789
                · linarith only [h0, h673, h676, h789, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h791 | h791
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h792 | h792
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h793 | h793
                      · linarith only [h0, h672, h676, h791, h793, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h672, h791, h793, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h672, h791, h792, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h672, h791, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · linarith only [h0, h672, h675, hc13, hlam, hphi, ht34, u4elo2]
      · linarith only [h0, h672, h674, hlam]
    · linarith only [h672, h673, hc13, hlam, hphi, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h801 | h801
    · rcases m.htr 0 2 3 (by decide) (by decide) with h802 | h802
      · rcases m.htr 0 2 4 (by decide) (by decide) with h803 | h803
        · rcases m.htr 0 2 5 (by decide) (by decide) with h804 | h804
          · rcases m.htr 0 3 4 (by decide) (by decide) with h805 | h805
            · rcases m.htr 0 3 5 (by decide) (by decide) with h806 | h806
              · rcases m.htr 0 4 5 (by decide) (by decide) with h807 | h807
                · rcases m.htr 1 2 3 (by decide) (by decide) with h808 | h808
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h809 | h809
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h810 | h810
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h811 | h811
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h812 | h812
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h813 | h813
                            · linarith only [h672, h801, h808, h809, h813, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h807, h811, h813, hc34, hlam, hphi, u4elo0]
                          · linarith only [h672, h801, h806, h807, h808, h811, h812, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h817 | h817
                          · linarith only [h672, h805, h808, h811, h817, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h819 | h819
                            · linarith only [h672, h801, h808, h809, h819, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h672, h801, h807, h808, h819, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h672, h808, h810, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h672, h808, h809, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h801, h808, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h825 | h825
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h826 | h826
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h827 | h827
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h828 | h828
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h829 | h829
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h830 | h830
                            · linarith only [h672, h801, h807, h826, h830, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases h0bigk with h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [hlam, p832_0]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h0, hlam, p832_1]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h672, hlam, p832_0]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h672, h801, h825, h826, h828, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p832_1, u2elo1]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h672, h801, h807, h825, h826, h828, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p832_1, u2elo1]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p832_1, u2elo1]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [hlam, p832_0]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p832_1, u2elo1]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h0, h801, h826, h828, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p832_1, u2elo1]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h0, h801, h807, h826, h828, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p832_1, u2elo1]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h801, h826, h828, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p832_1]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h802, hlam, p832_1]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [hlam, p832_0]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h672, h801, h825, h826, h828, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p832_1, u2elo1]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h672, h801, h807, h825, h826, h828, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p832_1, u2elo1]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h801, hlam, p832_0]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h803, hlam, p832_0]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h805, hlam, p832_0]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [hlam, p832_0]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h807, hlam, p832_0]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h801, h826, h828, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p832_1]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h804, hlam, p832_1]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h806, hlam, p832_0]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [h801, h807, h826, h828, hc34, hlam, hphi, p832_1, u4elo4]
                              · have p832_0 := h832c.1
                                have p832_1 := h832c.2.1
                                have p832_2 := h832c.2.2.1
                                have p832_3 := h832c.2.2.2
                                linarith only [hlam, p832_0]
                          · linarith only [h672, h806, h825, h828, h829, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h805, h807, h828, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h804, h827, hlam]
                    · linarith only [h672, h825, h826, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h801, h825, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h863 | h863
                · linarith only [h672, h801, h806, h863, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h865 | h865
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h866 | h866
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h867 | h867
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h868 | h868
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h869 | h869
                          · linarith only [h802, h806, h869, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h871 | h871
                            · linarith only [h672, h801, h863, h866, h871, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases h0bigk with h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [hlam, p873_0]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h0, hlam, p873_1]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h672, hlam, p873_0]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h672, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p873_1]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h672, h806, h865, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p873_1, u2elo1]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p873_1, u2elo1]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [hlam, p873_0]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h0, h672, h801, h866, h868, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p873_1, u2elo1]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h0, h801, h866, h868, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p873_1, u2elo1]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h0, h672, h801, h806, h866, h868, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p873_1, u2elo1]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h801, h866, h868, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p873_1]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h802, hlam, p873_1]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [hlam, p873_0]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h672, h801, h865, h866, h868, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p873_1, u2elo1]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h806, hlam, p873_1]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h801, hlam, p873_0]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h803, hlam, p873_0]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h805, hlam, p873_0]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [hlam, p873_0]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h863, hlam, p873_0]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h801, h863, h866, h868, hc34, hlam, hphi, p873_1, u4elo4]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h804, hlam, p873_1]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h863, hc03, hlam, hphi, ht34, p873_1, u4elo4]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [h801, h863, h866, h868, hc34, hlam, hphi, p873_1, u4elo4]
                              · have p873_0 := h873c.1
                                have p873_1 := h873c.2.1
                                have p873_2 := h873c.2.2.1
                                have p873_3 := h873c.2.2.2
                                linarith only [hlam, p873_0]
                        · linarith only [h805, h806, h868, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h804, h867, hlam]
                    · linarith only [h672, h865, h866, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h801, h865, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h672, h801, h805, hc14, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h904 | h904
            · rcases m.htr 0 3 5 (by decide) (by decide) with h905 | h905
              · linarith only [h802, h804, h905, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h907 | h907
                · linarith only [h672, h801, h802, h804, h907, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h909 | h909
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h910 | h910
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h911 | h911
                      · linarith only [h672, h801, h802, h804, h910, h911, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h801, h910, h911, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · linarith only [h672, h801, h909, h910, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                  · linarith only [h0, h801, h909, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h672, h801, h904, hc14, hlam, hphi, u4elo3]
        · linarith only [h802, h803, hc23, hlam, hphi, ht34, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h918 | h918
        · rcases m.htr 0 2 5 (by decide) (by decide) with h919 | h919
          · rcases m.htr 0 3 4 (by decide) (by decide) with h920 | h920
            · rcases m.htr 0 3 5 (by decide) (by decide) with h921 | h921
              · rcases m.htr 0 4 5 (by decide) (by decide) with h922 | h922
                · rcases m.htr 1 2 3 (by decide) (by decide) with h923 | h923
                  · linarith only [h0, h801, h802, h923, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h801, h923, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h926 | h926
                  · linarith only [h0, h801, h802, h926, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h801, h926, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h802, h919, h921, hlam]
            · linarith only [h0, h801, h802, h920, hc14, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h931 | h931
            · rcases m.htr 0 3 5 (by decide) (by decide) with h932 | h932
              · rcases m.htr 0 4 5 (by decide) (by decide) with h933 | h933
                · linarith only [h0, h801, h919, h933, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h935 | h935
                  · linarith only [h0, h801, h802, h935, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h801, h935, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h938 | h938
                · linarith only [h672, h801, h932, h938, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h940 | h940
                  · linarith only [h0, h801, h802, h940, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h801, h940, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h0, h801, h802, h931, hc14, hlam, hphi, u4elo3]
        · linarith only [h0, h801, h918, hc14, hlam, hphi, u4elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h945 | h945
      · rcases m.htr 0 2 4 (by decide) (by decide) with h946 | h946
        · rcases m.htr 0 2 5 (by decide) (by decide) with h947 | h947
          · rcases m.htr 0 3 4 (by decide) (by decide) with h948 | h948
            · rcases m.htr 0 3 5 (by decide) (by decide) with h949 | h949
              · rcases m.htr 0 4 5 (by decide) (by decide) with h950 | h950
                · rcases m.htr 1 2 3 (by decide) (by decide) with h951 | h951
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h952 | h952
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h953 | h953
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h954 | h954
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h955 | h955
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h956 | h956
                            · rcases h0bigk with h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [hlam, p957_0]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h0, hlam, p957_1]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h672, hlam, p957_0]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h801, hlam, p957_1]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h801, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p957_1, u4elo1]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p957_1, u2elo1]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [hlam, p957_0]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p957_1, u2elo1]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h0, h801, hc01, hlam, hphi, ht12, p957_1, u2elo1]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p957_1, u2elo1]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h672, h951, hc01, hlam, hphi, ht12, p957_1, u2elo1]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h945, hlam, p957_1]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [hlam, p957_0]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h672, h951, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p957_1, u2elo1]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h672, h951, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p957_1, u2elo1]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p957_1, u4elo0]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h946, hlam, p957_0]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h948, hlam, p957_0]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [hlam, p957_0]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h801, h947, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p957_1, u4elo1]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h0, h947, hc01, hlam, hphi, ht12, p957_1, u2elo1]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h947, hlam, p957_1]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h949, hlam, p957_0]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [h950, hlam, p957_1]
                              · have p957_0 := h957c.1
                                have p957_1 := h957c.2.1
                                have p957_2 := h957c.2.2.1
                                have p957_3 := h957c.2.2.2
                                linarith only [hlam, p957_0]
                            · linarith only [h801, h950, h956, hc24, hlam, hphi, u4elo1]
                          · linarith only [h672, h949, h951, h954, h955, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h985 | h985
                          · linarith only [h672, h948, h951, h954, h985, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h987 | h987
                            · rcases h0bigk with h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h0, hlam, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h672, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h801, hlam, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p988_1, u2elo1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p988_1, u2elo1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p988_1, u2elo1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p988_1, u2elo1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p988_1, u2elo1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h672, h951, hc01, hlam, hphi, ht12, p988_1, u2elo1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h945, hlam, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h672, h946, h951, h987, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p988_1, u2elo1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h672, h947, h951, h985, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p988_1, u2elo1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p988_1, u4elo0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h946, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h948, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h801, h949, h985, hc23, hlam, hphi, ht34, p988_1, u4elo1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h0, h947, hc01, hlam, hphi, ht12, p988_1, u2elo1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h947, hlam, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h949, hlam, p988_0]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [h950, hlam, p988_1]
                              · have p988_0 := h988c.1
                                have p988_1 := h988c.2.1
                                have p988_2 := h988c.2.2.1
                                have p988_3 := h988c.2.2.2
                                linarith only [hlam, p988_0]
                            · linarith only [h801, h950, h987, hc24, hlam, hphi, u4elo1]
                      · linarith only [h0, h953, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h672, h951, h952, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h951, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1018 | h1018
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1019 | h1019
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1020 | h1020
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1021 | h1021
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1022 | h1022
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1023 | h1023
                            · linarith only [h1023, h950, hc04, hlam, hphi, u4elo2]
                            · rcases h0bigk with h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [hlam, p1025_0]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h0, hlam, p1025_1]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h672, hlam, p1025_0]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h801, hlam, p1025_1]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h672, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p1025_1]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1025_1]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [hlam, p1025_0]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1025_1, u2elo1]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1025_1, u2elo1]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1025_1, u2elo1]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h672, hc01, hc13, hlam, hphi, p1025_1]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h945, hlam, p1025_1]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [hlam, p1025_0]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h0, h945, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1025_1, u2elo1]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h0, h945, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1025_1, u2elo1]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p1025_1, u4elo0]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h946, hlam, p1025_0]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h948, hlam, p1025_0]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [hlam, p1025_0]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h950, hlam, p1025_0]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h0, h947, hc01, hlam, hphi, ht12, p1025_1, u2elo1]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h947, hlam, p1025_1]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h949, hlam, p1025_0]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [h0, h801, h947, hc01, hlam, hphi, ht12, p1025_1, u2elo1]
                              · have p1025_0 := h1025c.1
                                have p1025_1 := h1025c.2.1
                                have p1025_2 := h1025c.2.2.1
                                have p1025_3 := h1025c.2.2.2
                                linarith only [hlam, p1025_0]
                          · linarith only [h0, h1021, h1022, h945, h949, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h1021, h948, h950, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1020, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1018, h1019, h672, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1018, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1056 | h1056
                · linarith only [h1056, h948, h949, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1058 | h1058
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1059 | h1059
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1060 | h1060
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1061 | h1061
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1062 | h1062
                          · linarith only [h1062, h945, h949, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1064 | h1064
                            · linarith only [h1056, h1064, h946, hlam]
                            · rcases h0bigk with h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [hlam, p1066_0]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h0, hlam, p1066_1]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h672, hlam, p1066_0]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h801, hlam, p1066_1]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h1061, h945, h949, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1066_1]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1066_1]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [hlam, p1066_0]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h0, h1061, h945, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1066_1, u2elo1]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1066_1, u2elo1]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h0, h1061, h945, h949, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1066_1, u2elo1]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h949, hc01, hc35, hlam, hphi, ht12, ht23, p1066_1]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h945, hlam, p1066_1]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [hlam, p1066_0]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h0, h801, h945, hc01, hlam, hphi, ht12, p1066_1, u2elo1]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h949, hlam, p1066_1]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p1066_1, u4elo0]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h946, hlam, p1066_0]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h948, hlam, p1066_0]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [hlam, p1066_0]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h1056, hlam, p1066_0]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h0, h1056, h1061, h1062, h947, hc01, hc34, hlam, hphi, ht12, p1066_1, u2elo1, u4elo4]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h947, hlam, p1066_1]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h1056, hc03, hlam, hphi, ht34, p1066_1, u4elo4]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [h1056, hc04, hlam, hphi, p1066_1, u4elo4]
                              · have p1066_0 := h1066c.1
                                have p1066_1 := h1066c.2.1
                                have p1066_2 := h1066c.2.2.1
                                have p1066_3 := h1066c.2.2.2
                                linarith only [hlam, p1066_0]
                        · linarith only [h1061, h948, h949, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h1060, h947, hlam]
                    · linarith only [h0, h1059, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1058, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1096 | h1096
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1097 | h1097
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1098 | h1098
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1099 | h1099
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1100 | h1100
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1101 | h1101
                        · linarith only [h1101, h945, h948, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1103 | h1103
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1104 | h1104
                            · rcases h0bigk with h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [hlam, p1105_0]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h0, hlam, p1105_1]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h672, hlam, p1105_0]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h801, hlam, p1105_1]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h672, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p1105_1]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p1105_1, u2elo1]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [hlam, p1105_0]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h0, h1103, h945, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1105_1, u2elo1]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h0, h1103, h945, h948, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1105_1, u2elo1]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h0, h947, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1105_1, u2elo1]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h948, hc01, hlam, hphi, ht12, ht23, ht34, p1105_1, u4elo3]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h945, hlam, p1105_1]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [hlam, p1105_0]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h948, hlam, p1105_1]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h947, h948, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1105_1, u4elo3]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p1105_1, u4elo0]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h946, hlam, p1105_0]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h801, hc03, hlam, hphi, ht34, p1105_1, u4elo1]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [hlam, p1105_0]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h801, h947, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1105_1, u4elo1]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h0, h947, hc01, hlam, hphi, ht12, p1105_1, u2elo1]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h947, hlam, p1105_1]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h1096, hlam, p1105_0]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [h1097, hlam, p1105_1]
                              · have p1105_0 := h1105c.1
                                have p1105_1 := h1105c.2.1
                                have p1105_2 := h1105c.2.2.1
                                have p1105_3 := h1105c.2.2.2
                                linarith only [hlam, p1105_0]
                            · linarith only [h1097, h1104, h801, hc24, hlam, hphi, u4elo1]
                          · linarith only [h1096, h1103, h948, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h0, h1100, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1098, h1099, h672, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1098, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1096, h1097, h948, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1137 | h1137
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1138 | h1138
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1139 | h1139
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1140 | h1140
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1141 | h1141
                        · linarith only [h1141, h945, h948, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1143 | h1143
                          · linarith only [h1096, h1143, h945, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1145 | h1145
                            · rcases h0bigk with h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [hlam, p1146_0]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h0, hlam, p1146_1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h672, hlam, p1146_0]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h801, hlam, p1146_1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h1096, h672, hlam, p1146_1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1146_1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [hlam, p1146_0]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h0, h672, hc01, hlam, hphi, ht12, p1146_1, u2elo1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h0, h1096, h1137, h672, hc01, hlam, hphi, ht12, p1146_1, u2elo1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h0, h1096, h672, hc01, hlam, hphi, ht12, p1146_1, u2elo1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h948, hc01, hc34, hlam, hphi, ht12, ht23, p1146_1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h945, hlam, p1146_1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [hlam, p1146_0]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h948, hlam, p1146_1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h1096, hlam, p1146_1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h801, hc01, hlam, hphi, ht12, ht23, ht34, p1146_1, u4elo1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h946, hlam, p1146_0]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h801, hc03, hlam, hphi, ht34, p1146_1, u4elo1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [hlam, p1146_0]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h801, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1146_1, u4elo1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h0, h947, hc01, hlam, hphi, ht12, p1146_1, u2elo1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h947, hlam, p1146_1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h0, h672, h947, hc01, hlam, hphi, ht12, p1146_1, u2elo1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [h1137, hlam, p1146_1]
                              · have p1146_0 := h1146c.1
                                have p1146_1 := h1146c.2.1
                                have p1146_2 := h1146c.2.2.1
                                have p1146_3 := h1146c.2.2.2
                                linarith only [hlam, p1146_0]
                            · linarith only [h1137, h1145, h801, hc24, hlam, hphi, u4elo1]
                      · linarith only [h0, h1140, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1139, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1138, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1176 | h1176
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1177 | h1177
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1178 | h1178
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1179 | h1179
                        · linarith only [h1179, h945, h948, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1181 | h1181
                          · linarith only [h1096, h1181, h945, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1183 | h1183
                            · linarith only [h1137, h1183, h946, hlam]
                            · rcases h0bigk with h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [hlam, p1185_0]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h0, hlam, p1185_1]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h672, hlam, p1185_0]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h801, hlam, p1185_1]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h1137, h672, h948, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1185_1]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p1185_1, u2elo1]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [hlam, p1185_0]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h0, h672, hc01, hlam, hphi, ht12, p1185_1, u2elo1]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h0, h672, h948, hc01, hlam, hphi, ht12, p1185_1, u2elo1]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h0, h1137, h672, h948, hc01, hlam, hphi, ht12, p1185_1, u2elo1]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h1096, hc01, hc35, hlam, hphi, ht12, ht23, p1185_1]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h945, hlam, p1185_1]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [hlam, p1185_0]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h948, hlam, p1185_1]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h1096, hlam, p1185_1]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h1137, hc01, hlam, hphi, ht12, ht23, ht34, p1185_1, u4elo4]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h946, hlam, p1185_0]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h1137, hc03, hlam, hphi, ht34, p1185_1, u4elo4]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [hlam, p1185_0]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h1137, hlam, p1185_0]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h0, h947, hc01, hlam, hphi, ht12, p1185_1, u2elo1]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h947, hlam, p1185_1]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h0, h672, h947, hc01, hlam, hphi, ht12, p1185_1, u2elo1]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [h1137, hc04, hlam, hphi, p1185_1, u4elo4]
                              · have p1185_0 := h1185c.1
                                have p1185_1 := h1185c.2.1
                                have p1185_2 := h1185c.2.2.1
                                have p1185_3 := h1185c.2.2.2
                                linarith only [hlam, p1185_0]
                      · linarith only [h0, h1178, h947, hlam]
                    · linarith only [h0, h1177, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1176, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1214 | h1214
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1215 | h1215
              · linarith only [h1215, h945, h947, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1217 | h1217
                · linarith only [h1217, h946, h947, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1219 | h1219
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1220 | h1220
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1221 | h1221
                      · linarith only [h1221, h947, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1221, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1219, h1220, h672, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h1219, h945, h947, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1226 | h1226
              · linarith only [h1226, h945, h947, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1228 | h1228
                · linarith only [h1228, h946, h947, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1230 | h1230
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1231 | h1231
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1232 | h1232
                      · linarith only [h1232, h947, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1232, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1230, h1231, h672, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1230, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h945, h946, hc23, hlam, hphi, ht34, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1238 | h1238
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1239 | h1239
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1240 | h1240
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1241 | h1241
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1242 | h1242
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1243 | h1243
                  · linarith only [h1238, h1243, h945, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1243, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1246 | h1246
                  · linarith only [h1238, h1246, h945, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1246, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1239, h1241, h945, hlam]
            · linarith only [h1238, h1240, h945, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1251 | h1251
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1252 | h1252
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1253 | h1253
                · linarith only [h1238, h1239, h1253, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1255 | h1255
                  · linarith only [h1238, h1255, h945, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1255, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1258 | h1258
                · linarith only [h1238, h1252, h1258, h945, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1260 | h1260
                  · linarith only [h1238, h1260, h945, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1260, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h1238, h1251, h945, hc24, hlam, hphi, u4elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1264 | h1264
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1265 | h1265
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1266 | h1266
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1267 | h1267
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1268 | h1268
                  · linarith only [h1268, h945, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1268, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1238, h1264, h1267, hlam]
              · linarith only [h1264, h1266, h945, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1273 | h1273
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1274 | h1274
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1275 | h1275
                  · linarith only [h1275, h945, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1275, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1264, h1265, h1274, h945, hlam]
              · linarith only [h1264, h1273, h945, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1280 | h1280
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1281 | h1281
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1282 | h1282
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1283 | h1283
                  · linarith only [h1283, h945, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1283, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1286 | h1286
                  · linarith only [h0, h1286, h945, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1286, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1289 | h1289
                · linarith only [h1280, h1281, h1289, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1291 | h1291
                  · linarith only [h0, h1291, h945, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1291, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1294 | h1294
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1295 | h1295
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1296 | h1296
                  · linarith only [h0, h1296, h945, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1296, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1280, h1294, h1295, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1300 | h1300
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1301 | h1301
                  · linarith only [h0, h1301, h945, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1301, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1304 | h1304
                  · linarith only [h0, h1304, h945, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1304, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_20_12_14_H_I_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2elo := hb2.1
  have h4elo := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_14_H_I_L_0_L_0_x0 m hb0 hb2 hb4 h0
  · exact r1l7_20_12_14_H_I_L_0_L_0_x1 m hb0 hb2 hb4 h0

theorem r1l7_20_12_14_M_LI_L_R_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                    · linarith only [h0, h10, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                    · linarith only [h0, h10, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
                    · linarith only [h0, h13, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                    · linarith only [h0, h13, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h16 | h16
                  · linarith only [h16, h7, h8, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                    · linarith only [h0, h18, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                    · linarith only [h18, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h21 | h21
                · rcases m.htr 0 4 5 (by decide) (by decide) with h22 | h22
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                    · linarith only [h0, h23, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                    · linarith only [h0, h23, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                  · linarith only [h21, h22, h7, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h27 | h27
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
                    · linarith only [h0, h28, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                    · linarith only [h0, h28, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                    · linarith only [h0, h31, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                    · linarith only [h0, h31, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
            · linarith only [h5, h6, hc25, hlam, hphi, u2ehi3]
          · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h36 | h36
          · linarith only [h36, h4, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h38 | h38
            · linarith only [h38, h4, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h40 | h40
              · rcases m.htr 0 3 5 (by decide) (by decide) with h41 | h41
                · rcases m.htr 0 4 5 (by decide) (by decide) with h42 | h42
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h43 | h43
                    · linarith only [h0, h4, h43, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h46 | h46
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h48 | h48
                            · rcases h0bigk with h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [hlam, p49_0]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p49_1, u0elo0, u2ehi1]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h40, hc34, hlam, hphi, ht0b, ht45, ht5b, p49_1, u0elo0]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h0, h36, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p49_1, u0elo0, u2ehi1]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h0, h38, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p49_1, u0elo0, u2ehi1]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h0, hlam, p49_0]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [hlam, p49_0]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h4, hlam, p49_0]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h36, hlam, p49_1]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h38, hlam, p49_0]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h1, hlam, p49_1]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p49_1, u0elo2, u2ehi1]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [hlam, p49_0]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h0, h36, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p49_1, u0elo2, u2ehi1]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h0, h1, h38, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p49_1, u0elo0, u2ehi1]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h2, hlam, p49_0]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p49_1, u0elo3, u2ehi1]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h40, hlam, p49_0]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [hlam, p49_0]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h0, h1, h38, h40, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p49_1, u0elo0, u2ehi1]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h3, hlam, p49_0]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p49_1, u0elo4, u2ehi1]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h41, hlam, p49_0]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [h42, hlam, p49_1]
                              · have p49_0 := h49c.1
                                have p49_1 := h49c.2.1
                                have p49_2 := h49c.2.2.1
                                have p49_3 := h49c.2.2.2
                                linarith only [hlam, p49_0]
                            · rcases h0bigk with h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [hlam, p75_0]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p75_1, u0elo0, u2ehi1]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h0, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p75_1, u0elo0, u2ehi1]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h0, h36, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p75_1, u0elo0, u2ehi1]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h0, h38, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p75_1, u0elo0, u2ehi1]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h0, hlam, p75_0]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [hlam, p75_0]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h4, hlam, p75_0]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h36, hlam, p75_1]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h38, hlam, p75_0]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h1, hlam, p75_1]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p75_1, u0elo2, u2ehi1]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [hlam, p75_0]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h0, h36, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p75_1, u0elo2, u2ehi1]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h0, h1, h38, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p75_1, u0elo0, u2ehi1]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h2, hlam, p75_0]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p75_1, u0elo3, u2ehi1]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h40, hlam, p75_0]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [hlam, p75_0]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h0, h1, h38, h40, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p75_1, u0elo0, u2ehi1]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h3, hlam, p75_0]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p75_1, u0elo4, u2ehi1]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h41, hlam, p75_0]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [h42, hlam, p75_1]
                              · have p75_0 := h75c.1
                                have p75_1 := h75c.2.1
                                have p75_2 := h75c.2.2.1
                                have p75_3 := h75c.2.2.2
                                linarith only [hlam, p75_0]
                          · linarith only [h0, h36, h47, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                        · linarith only [h0, h4, h46, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h0, h4, h45, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h104 | h104
                    · linarith only [h0, h104, h4, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h108 | h108
                          · linarith only [h0, h106, h108, h36, h42, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h0, h108, h36, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                        · linarith only [h1, h107, h41, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                      · linarith only [h0, h106, h2, h4, h40, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h113 | h113
                  · linarith only [h113, h40, h41, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h115 | h115
                    · linarith only [h0, h115, h4, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                        · linarith only [h0, h118, h4, h41, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h118, h4, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h0, h117, h4, h40, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h122 | h122
                · rcases m.htr 0 4 5 (by decide) (by decide) with h123 | h123
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h124 | h124
                    · linarith only [h0, h124, h4, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h126 | h126
                      · linarith only [h0, h122, h126, h38, h40, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h0, h126, h4, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h122, h123, h40, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h130 | h130
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h131 | h131
                    · linarith only [h0, h131, h4, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h133 | h133
                      · linarith only [h0, h133, h4, h40, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h0, h133, h4, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h136 | h136
                    · linarith only [h0, h136, h4, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h138 | h138
                      · linarith only [h0, h138, h4, h40, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h0, h138, h4, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h141 | h141
        · rcases m.htr 0 2 4 (by decide) (by decide) with h142 | h142
          · rcases m.htr 0 2 5 (by decide) (by decide) with h143 | h143
            · linarith only [h0, h143, h3, hlam]
            · linarith only [h141, h143, hc25, hlam, hphi, u2ehi2]
          · linarith only [h141, h142, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h147 | h147
          · linarith only [h141, h147, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h149 | h149
            · linarith only [h141, h149, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h151 | h151
              · rcases m.htr 0 3 5 (by decide) (by decide) with h152 | h152
                · linarith only [h1, h152, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h154 | h154
                  · linarith only [h0, h151, h152, h154, h3, hc35, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h156 | h156
                    · linarith only [h0, h141, h156, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h158 | h158
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h159 | h159
                        · linarith only [h1, h152, h156, h159, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h141, h159, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h0, h141, h151, h158, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h163 | h163
                · linarith only [h0, h151, h163, h3, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h165 | h165
                  · linarith only [h165, h2, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h167 | h167
                    · linarith only [h0, h141, h167, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h169 | h169
                      · linarith only [h1, h151, h167, h169, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h0, h141, h169, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h172 | h172
      · rcases m.htr 0 2 3 (by decide) (by decide) with h173 | h173
        · rcases m.htr 0 2 4 (by decide) (by decide) with h174 | h174
          · linarith only [h0, h174, h2, hlam]
          · linarith only [h173, h174, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h177 | h177
          · linarith only [h173, h177, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h179 | h179
            · linarith only [h173, h179, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h181 | h181
              · linarith only [h1, h181, h2, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h183 | h183
                · rcases m.htr 0 4 5 (by decide) (by decide) with h184 | h184
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h185 | h185
                    · linarith only [h0, h185, h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h187 | h187
                      · linarith only [h179, h181, h183, h187, hc23, hlam, hphi, u2ehi0]
                      · linarith only [h0, h173, h187, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h0, h184, h2, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h191 | h191
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h192 | h192
                    · linarith only [h0, h173, h192, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h194 | h194
                      · linarith only [h1, h181, h192, h194, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h0, h173, h194, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h0, h191, h2, hc45, hlam, hphi, ht23, ht34, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h198 | h198
        · rcases m.htr 0 2 4 (by decide) (by decide) with h199 | h199
          · linarith only [h0, h199, h2, hlam]
          · linarith only [h198, h199, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h202 | h202
          · linarith only [h198, h202, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h204 | h204
            · linarith only [h198, h204, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h206 | h206
              · linarith only [h1, h2, h206, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h208 | h208
                · linarith only [h0, h172, h206, h208, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h210 | h210
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h211 | h211
                    · linarith only [h0, h211, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h213 | h213
                      · linarith only [h198, h206, h213, hc23, hlam, hphi, u2ehi0]
                      · linarith only [h0, h198, h213, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h0, h2, h210, hc45, hlam, hphi, ht23, ht34, u2ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h217 | h217
    · rcases m.htr 0 1 5 (by decide) (by decide) with h218 | h218
      · rcases m.htr 0 2 3 (by decide) (by decide) with h219 | h219
        · linarith only [h0, h1, h219, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h221 | h221
          · linarith only [h219, h221, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h223 | h223
            · linarith only [h219, h223, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h225 | h225
              · rcases m.htr 0 3 5 (by decide) (by decide) with h226 | h226
                · rcases m.htr 0 4 5 (by decide) (by decide) with h227 | h227
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h228 | h228
                    · linarith only [h0, h219, h228, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                    · linarith only [h0, h1, h228, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h231 | h231
                    · linarith only [h0, h231, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                    · linarith only [h0, h1, h231, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h226, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h225, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h236 | h236
        · linarith only [h0, h1, h236, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h238 | h238
          · linarith only [h236, h238, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h240 | h240
            · linarith only [h238, h240, hc24, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h242 | h242
              · rcases m.htr 0 3 5 (by decide) (by decide) with h243 | h243
                · rcases m.htr 0 4 5 (by decide) (by decide) with h244 | h244
                  · linarith only [h217, h218, h244, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h246 | h246
                    · linarith only [h0, h218, h243, h246, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                    · linarith only [h0, h1, h246, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h243, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h242, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h251 | h251
      · rcases m.htr 0 2 3 (by decide) (by decide) with h252 | h252
        · linarith only [h0, h1, h252, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h254 | h254
          · linarith only [h252, h254, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h256 | h256
            · linarith only [h252, h256, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h258 | h258
              · rcases m.htr 0 3 5 (by decide) (by decide) with h259 | h259
                · rcases m.htr 0 4 5 (by decide) (by decide) with h260 | h260
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h261 | h261
                    · linarith only [h0, h217, h252, h258, h261, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                    · linarith only [h0, h1, h261, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h217, h260, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h217, h258, h259, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h258, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h267 | h267
        · linarith only [h0, h1, h267, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h269 | h269
          · linarith only [h267, h269, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h271 | h271
            · linarith only [h267, h271, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h273 | h273
              · rcases m.htr 0 3 5 (by decide) (by decide) with h274 | h274
                · rcases m.htr 0 4 5 (by decide) (by decide) with h275 | h275
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h276 | h276
                    · linarith only [h0, h251, h267, h273, h275, h276, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                    · linarith only [h0, h1, h276, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h217, h275, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h217, h273, h274, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h273, hc34, hlam, hphi, ht23, u2ehi1]

end R2N4
