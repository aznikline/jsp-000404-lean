import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_37S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7292000 in
set_option maxHeartbeats 7292000 in
theorem r1l7_12_24_L_I_M_LI_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h696 | h696
  · rcases m.htr 0 2 5 (by decide) (by decide) with h697 | h697
    · rcases m.htr 0 3 4 (by decide) (by decide) with h698 | h698
      · rcases m.htr 0 4 5 (by decide) (by decide) with h699 | h699
        · rcases m.htr 1 2 3 (by decide) (by decide) with h700 | h700
          · linarith only [h0, h3, h696, h700, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h702 | h702
            · rcases m.htr 1 3 4 (by decide) (by decide) with h703 | h703
              · rcases m.htr 1 3 5 (by decide) (by decide) with h704 | h704
                · rcases m.htr 1 4 5 (by decide) (by decide) with h705 | h705
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h706 | h706
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h707 | h707
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h708 | h708
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h709 | h709
                          · rcases h2bigk with h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [hlam, p710_0]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [h702, h706, h709, hc02, hc45, hlam, hphi, ht0b, ht5b, p710_1]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [h3, hlam, p710_0]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [h3, h706, h709, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p710_1]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              rcases p710_3 (m.d 0 2) (by simp) with h715 | h715
                              · rcases p710_3 (m.d 1 2) (by simp) with h716 | h716
                                · linarith only [h0, h716, hlam]
                                · linarith only [h3, h702, h706, h709, h716, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p710_1]
                              · linarith only [h715, hlam, p710_0]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [h0, hlam, p710_1]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [hlam, p710_0]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [h700, hlam, p710_0]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [h0, h706, h709, hc01, hc45, hlam, hphi, ht0b, ht5b, p710_1]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              rcases p710_3 (m.d 0 2) (by simp) with h724 | h724
                              · rcases p710_3 (m.d 1 2) (by simp) with h725 | h725
                                · rcases p710_3 (m.d 2 3) (by simp) with h726 | h726
                                  · rcases p710_3 (m.d 2 4) (by simp) with h727 | h727
                                    · linarith only [h702, h727, hlam]
                                    · linarith only [h708, h727, hlam]
                                  · linarith only [h707, h726, hlam]
                                · linarith only [h725, hlam, p710_0]
                              · linarith only [h697, h724, hlam]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [h696, h706, h709, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p710_1]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [h702, h706, h709, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p710_1]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [hlam, p710_0]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              rcases p710_3 (m.d 0 2) (by simp) with h736 | h736
                              · linarith only [h3, h736, hlam]
                              · linarith only [h696, h736, hlam]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              rcases p710_3 (m.d 0 2) (by simp) with h739 | h739
                              · linarith only [h3, h739, hlam]
                              · linarith only [h697, h739, hlam]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [h696, hlam, p710_0]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [h702, hlam, p710_0]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [h706, hlam, p710_0]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [hlam, p710_0]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [h0, h702, hc01, hc25, hlam, hphi, ht0b, ht5b, p710_1]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [h697, hlam, p710_0]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [h702, h706, h709, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p710_1]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [h707, hlam, p710_0]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [h708, hlam, p710_1]
                            · have p710_0 := h710c.1
                              have p710_1 := h710c.2.1
                              have p710_2 := h710c.2.2.1
                              have p710_3 := h710c.2.2.2
                              linarith only [hlam, p710_0]
                          · linarith only [h1, h700, h702, h708, h709, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h2, h705, h708, hc24, hlam, hphi, u4elo0]
                      · linarith only [h0, h1, h3, h702, h704, h706, h707, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h3, h702, h706, hc24, hlam, hphi, u4elo3]
                  · linarith only [h699, h703, h705, hc34, hlam, hphi, u4elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h757 | h757
                  · linarith only [h700, h702, h704, h757, hlam]
                  · linarith only [h699, h757, hc14, hlam, hphi, u4elo0]
              · linarith only [h700, h702, h703, hc24, hlam, hphi, u4elo3]
            · linarith only [h3, h696, h702, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h762 | h762
          · linarith only [h0, h3, h696, h762, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h764 | h764
            · rcases m.htr 1 3 4 (by decide) (by decide) with h765 | h765
              · rcases m.htr 1 3 5 (by decide) (by decide) with h766 | h766
                · rcases m.htr 1 4 5 (by decide) (by decide) with h767 | h767
                  · linarith only [h2, h699, h767, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h769 | h769
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h770 | h770
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h771 | h771
                        · linarith only [h0, h2, h3, h699, h764, h771, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h773 | h773
                          · linarith only [h2, h699, h764, h769, h773, hlam]
                          · rcases h2bigk with h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              linarith only [hlam, p775_0]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              linarith only [h3, hc12, hc23, hlam, hphi, p775_1]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              linarith only [h3, hlam, p775_0]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              rcases p775_3 (m.d 0 2) (by simp) with h779 | h779
                              · rcases p775_3 (m.d 1 2) (by simp) with h780 | h780
                                · linarith only [h0, h780, hlam]
                                · linarith only [h764, h780, hlam]
                              · linarith only [h779, hlam, p775_0]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              rcases p775_3 (m.d 0 2) (by simp) with h784 | h784
                              · rcases p775_3 (m.d 1 2) (by simp) with h785 | h785
                                · linarith only [h0, h785, hlam]
                                · linarith only [h3, h764, h769, h785, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p775_1]
                              · linarith only [h784, hlam, p775_0]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              linarith only [h0, hlam, p775_1]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              linarith only [hlam, p775_0]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              linarith only [h762, hlam, p775_0]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              rcases p775_3 (m.d 0 2) (by simp) with h792 | h792
                              · rcases p775_3 (m.d 1 2) (by simp) with h793 | h793
                                · rcases p775_3 (m.d 2 3) (by simp) with h794 | h794
                                  · rcases p775_3 (m.d 2 4) (by simp) with h795 | h795
                                    · linarith only [h795, hlam, p775_0]
                                    · rcases p775_3 (m.d 2 5) (by simp) with h797 | h797
                                      · linarith only [h3, h697, h769, h797, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p775_1]
                                      · linarith only [h771, h797, hlam]
                                  · linarith only [h769, h794, hlam]
                                · linarith only [h793, hlam, p775_0]
                              · linarith only [h696, h792, hlam]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              rcases p775_3 (m.d 0 2) (by simp) with h803 | h803
                              · rcases p775_3 (m.d 1 2) (by simp) with h804 | h804
                                · rcases p775_3 (m.d 2 3) (by simp) with h805 | h805
                                  · rcases p775_3 (m.d 2 4) (by simp) with h806 | h806
                                    · linarith only [h764, h806, hlam]
                                    · rcases p775_3 (m.d 2 5) (by simp) with h808 | h808
                                      · linarith only [h808, hlam, p775_0]
                                      · rcases h4bigk with h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [hlam, p810_0]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [h699, h764, h769, hc34, hlam, hphi, p810_1, u4elo4]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [h699, h769, hc34, hlam, hphi, p810_1, u4elo4]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [h699, hc34, hlam, hphi, p810_1, u4elo4]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [h699, hlam, p810_0]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [h2, hlam, p810_0]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [hlam, p810_0]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [h769, hc34, hlam, hphi, p810_1, u4elo1]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [h2, h699, hc34, hlam, hphi, p810_1, u4elo4]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [h767, hlam, p810_0]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [h696, hlam, p810_0]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [h764, hlam, p810_0]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [hlam, p810_0]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [hc34, hlam, hphi, p810_1, u4elo2]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [h771, hlam, p810_0]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [h698, hlam, p810_0]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [h765, hlam, p810_0]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [h769, hlam, p810_0]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [hlam, p810_0]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [h773, hlam, p810_0]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [hc04, hlam, hphi, p810_1, u4elo4]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [h764, hc24, hlam, hphi, p810_1, u4elo4]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [h769, hc34, hlam, hphi, p810_1, u4elo4]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [hc34, hlam, hphi, p810_1, u4elo4]
                                        · have p810_0 := h810c.1
                                          have p810_1 := h810c.2.1
                                          have p810_2 := h810c.2.2.1
                                          have p810_3 := h810c.2.2.2
                                          linarith only [hlam, p810_0]
                                  · linarith only [h770, h805, hlam]
                                · linarith only [h804, hlam, p775_0]
                              · linarith only [h697, h803, hlam]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              rcases p775_3 (m.d 0 2) (by simp) with h839 | h839
                              · linarith only [h839, hlam, p775_0]
                              · rcases p775_3 (m.d 1 2) (by simp) with h841 | h841
                                · linarith only [h762, h841, hlam]
                                · rcases p775_3 (m.d 2 3) (by simp) with h843 | h843
                                  · rcases p775_3 (m.d 2 4) (by simp) with h844 | h844
                                    · linarith only [h769, h844, hlam]
                                    · rcases p775_3 (m.d 2 5) (by simp) with h846 | h846
                                      · linarith only [h770, h846, hlam]
                                      · rcases h4bigk with h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [hlam, p848_0]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [h764, h769, hc34, hlam, hphi, p848_1, u4elo0]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [h696, h769, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p775_1, p848_1]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [h696, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p775_1, p848_1]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [h699, hlam, p848_0]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [h2, hlam, p848_0]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [hlam, p848_0]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [h769, hc34, hlam, hphi, p848_1, u4elo1]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [h2, h699, hc34, hlam, hphi, p848_1, u4elo4]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [h767, hlam, p848_0]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [h696, hlam, p848_0]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [h764, hlam, p848_0]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [hlam, p848_0]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [hc34, hlam, hphi, p848_1, u4elo2]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [h771, hlam, p848_0]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [h698, hlam, p848_0]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [h765, hlam, p848_0]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [h769, hlam, p848_0]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [hlam, p848_0]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [h773, hlam, p848_0]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [hc04, hlam, hphi, p848_1, u4elo4]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [h764, hc24, hlam, hphi, p848_1, u4elo4]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [h769, hc34, hlam, hphi, p848_1, u4elo4]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [hc34, hlam, hphi, p848_1, u4elo4]
                                        · have p848_0 := h848c.1
                                          have p848_1 := h848c.2.1
                                          have p848_2 := h848c.2.2.1
                                          have p848_3 := h848c.2.2.2
                                          linarith only [hlam, p848_0]
                                  · linarith only [h843, hlam, p775_0]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              rcases p775_3 (m.d 0 2) (by simp) with h875 | h875
                              · linarith only [h3, h875, hlam]
                              · linarith only [h0, h875, hlam]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              linarith only [hlam, p775_0]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              rcases p775_3 (m.d 0 2) (by simp) with h879 | h879
                              · linarith only [h3, h879, hlam]
                              · linarith only [h696, h879, hlam]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              rcases p775_3 (m.d 0 2) (by simp) with h882 | h882
                              · linarith only [h3, h882, hlam]
                              · linarith only [h697, h882, hlam]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              linarith only [h696, hlam, p775_0]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              linarith only [h764, hlam, p775_0]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              linarith only [h769, hlam, p775_0]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              linarith only [hlam, p775_0]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              linarith only [h771, hlam, p775_0]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              linarith only [h697, hlam, p775_0]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              linarith only [h697, h764, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p775_1]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              linarith only [h770, hlam, p775_0]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              linarith only [h3, h697, h769, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p775_1]
                            · have p775_0 := h775c.1
                              have p775_1 := h775c.2.1
                              have p775_2 := h775c.2.2.1
                              have p775_3 := h775c.2.2.2
                              linarith only [hlam, p775_0]
                      · linarith only [h3, h697, h766, h770, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h3, h769, hc02, hlam, hphi, ht23, ht34, u4elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h897 | h897
                  · linarith only [h2, h699, h897, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h899 | h899
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h900 | h900
                      · linarith only [h3, h697, h762, h764, h766, h899, h900, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h3, h697, h900, hlam]
                    · linarith only [h3, h899, hc02, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h698, h699, h762, h764, h765, hc24, hlam, hphi, u4elo4]
            · linarith only [h3, h696, h764, hc12, hc23, hlam, hphi]
      · linarith only [h3, h696, h698, hc24, hlam, hphi, u4elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h907 | h907
      · rcases m.htr 0 4 5 (by decide) (by decide) with h908 | h908
        · linarith only [h696, h697, h908, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h910 | h910
          · linarith only [h0, h3, h696, h910, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h912 | h912
            · rcases m.htr 1 3 4 (by decide) (by decide) with h913 | h913
              · rcases m.htr 1 3 5 (by decide) (by decide) with h914 | h914
                · rcases m.htr 1 4 5 (by decide) (by decide) with h915 | h915
                  · linarith only [h908, h915, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h917 | h917
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h918 | h918
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h919 | h919
                        · linarith only [h0, h2, h697, h908, h912, h918, h919, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h697, h912, h919, hc24, hlam, hphi, u4elo4]
                      · linarith only [h0, h1, h3, h912, h914, h917, h918, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h3, h912, h917, hc24, hlam, hphi, u4elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h924 | h924
                  · linarith only [h908, h924, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h926 | h926
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h927 | h927
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h928 | h928
                        · linarith only [h1, h908, h910, h912, h928, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h696, h697, h926, h928, hc34, hlam, hphi, u4elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h931 | h931
                        · linarith only [h0, h3, h912, h924, h927, h931, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h3, h912, h926, h927, h931, hc34, hlam, hphi, u4elo4]
                    · linarith only [h0, h3, h912, h926, hc24, hlam, hphi, u4elo3]
              · linarith only [h907, h910, h912, h913, hc24, hlam, hphi, u4elo0]
            · linarith only [h3, h696, h912, hc12, hc23, hlam, hphi]
      · linarith only [h3, h696, h907, hc24, hlam, hphi, u4elo3]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h938 | h938
    · rcases m.htr 0 3 4 (by decide) (by decide) with h939 | h939
      · rcases m.htr 0 4 5 (by decide) (by decide) with h940 | h940
        · rcases m.htr 1 2 3 (by decide) (by decide) with h941 | h941
          · linarith only [h0, h3, h938, h941, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h943 | h943
            · linarith only [h0, h696, h938, h943, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h945 | h945
              · rcases m.htr 1 3 5 (by decide) (by decide) with h946 | h946
                · rcases m.htr 1 4 5 (by decide) (by decide) with h947 | h947
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h948 | h948
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h949 | h949
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h950 | h950
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h951 | h951
                          · rcases h2bigk with h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [hlam, p952_0]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [h696, hc12, hlam, hphi, ht23, ht34, p952_1, u4elo2]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [h3, hlam, p952_0]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [h696, hlam, p952_0]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [h696, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p952_1, u4elo2]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [h0, hlam, p952_1]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [hlam, p952_0]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [h941, hlam, p952_0]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [h943, hlam, p952_0]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [h0, h696, h949, h951, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p952_1, u4elo2]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              rcases p952_3 (m.d 0 2) (by simp) with h963 | h963
                              · linarith only [h963, hlam, p952_0]
                              · rcases p952_3 (m.d 1 2) (by simp) with h965 | h965
                                · linarith only [h941, h965, hlam]
                                · rcases p952_3 (m.d 2 3) (by simp) with h967 | h967
                                  · rcases p952_3 (m.d 2 4) (by simp) with h968 | h968
                                    · linarith only [h948, h968, hlam]
                                    · linarith only [h696, h968, hlam]
                                  · linarith only [h967, hlam, p952_0]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              rcases p952_3 (m.d 0 2) (by simp) with h972 | h972
                              · linarith only [h3, h972, hlam]
                              · linarith only [h0, h972, hlam]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [hlam, p952_0]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [h696, hc02, hc23, hlam, hphi, p952_1]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              rcases p952_3 (m.d 0 2) (by simp) with h977 | h977
                              · linarith only [h3, h977, hlam]
                              · linarith only [h938, h977, hlam]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [h938, h949, h951, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p952_1, u4elo2]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, p952_1, u4elo2]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [h948, hlam, p952_0]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [hlam, p952_0]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              rcases p952_3 (m.d 0 2) (by simp) with h984 | h984
                              · linarith only [h696, h984, hlam]
                              · linarith only [h938, h984, hlam]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [h938, hlam, p952_0]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [h696, h938, hc12, hlam, hphi, ht23, ht34, p952_1, u4elo0]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [h949, hlam, p952_0]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [h950, hlam, p952_1]
                            · have p952_0 := h952c.1
                              have p952_1 := h952c.2.1
                              have p952_2 := h952c.2.2.1
                              have p952_3 := h952c.2.2.2
                              linarith only [hlam, p952_0]
                          · linarith only [h696, h940, h951, hc34, hlam, hphi, u4elo2]
                        · linarith only [h696, h938, h940, h950, hlam]
                      · linarith only [h1, h3, h946, h949, hlam]
                    · linarith only [h3, h948, hc02, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h696, h938, h940, h947, hc14, hlam, hphi, u4elo2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h997 | h997
                  · linarith only [h945, h946, h997, hlam]
                  · linarith only [h940, h997, hc14, hlam, hphi, u4elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1000 | h1000
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1001 | h1001
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1002 | h1002
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1003 | h1003
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1004 | h1004
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1005 | h1005
                          · rcases h2bigk with h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [hlam, p1006_0]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [h696, hc12, hlam, hphi, ht23, ht34, p1006_1, u4elo2]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [h3, hlam, p1006_0]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [h696, hlam, p1006_0]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [h1003, h1005, h696, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1006_1, u4elo2]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [h0, hlam, p1006_1]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [hlam, p1006_0]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [h941, hlam, p1006_0]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [h943, hlam, p1006_0]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [h0, h1003, h1005, h696, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1006_1, u4elo2]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              rcases p1006_3 (m.d 0 2) (by simp) with h1017 | h1017
                              · linarith only [h1017, hlam, p1006_0]
                              · rcases p1006_3 (m.d 1 2) (by simp) with h1019 | h1019
                                · linarith only [h1019, h941, hlam]
                                · rcases p1006_3 (m.d 2 3) (by simp) with h1021 | h1021
                                  · rcases p1006_3 (m.d 2 4) (by simp) with h1022 | h1022
                                    · linarith only [h1002, h1022, hlam]
                                    · linarith only [h1022, h696, hlam]
                                  · linarith only [h1021, hlam, p1006_0]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              rcases p1006_3 (m.d 0 2) (by simp) with h1026 | h1026
                              · linarith only [h1026, h3, hlam]
                              · linarith only [h0, h1026, hlam]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [hlam, p1006_0]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [h696, hc02, hc23, hlam, hphi, p1006_1]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              rcases p1006_3 (m.d 0 2) (by simp) with h1031 | h1031
                              · linarith only [h1031, h3, hlam]
                              · linarith only [h1031, h938, hlam]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [hc02, hlam, hphi, ht23, ht34, p1006_1, u4elo2]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, p1006_1, u4elo2]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [h1002, hlam, p1006_0]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [hlam, p1006_0]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              rcases p1006_3 (m.d 0 2) (by simp) with h1038 | h1038
                              · linarith only [h1038, h696, hlam]
                              · linarith only [h1038, h938, hlam]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [h938, hlam, p1006_0]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [h3, h938, hc12, hc23, hlam, hphi, p1006_1]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [h1003, hlam, p1006_0]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [h1004, hlam, p1006_1]
                            · have p1006_0 := h1006c.1
                              have p1006_1 := h1006c.2.1
                              have p1006_2 := h1006c.2.2.1
                              have p1006_3 := h1006c.2.2.2
                              linarith only [hlam, p1006_0]
                          · linarith only [h1000, h1005, h945, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h1000, h1001, h1004, h696, h939, h945, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h1000, h1003, h939, h945, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1002, h3, h939, hlam]
                  · linarith only [h1001, h696, h938, h940, hc14, hlam, hphi, u4elo2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1051 | h1051
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1052 | h1052
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1053 | h1053
                      · linarith only [h1000, h1053, h696, h938, hc13, hlam, hphi, ht34, u4elo2]
                      · linarith only [h1053, h3, h939, h941, h945, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h1052, h3, h939, hlam]
                  · linarith only [h1051, h696, h940, hc14, hlam, hphi, u4elo2]
        · linarith only [h696, h938, h940, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1059 | h1059
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1060 | h1060
          · linarith only [h0, h1060, h3, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1062 | h1062
            · linarith only [h0, h1062, h3, h939, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1064 | h1064
              · linarith only [h1, h1064, h3, h938, h939, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1066 | h1066
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1067 | h1067
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1068 | h1068
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1069 | h1069
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1070 | h1070
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1071 | h1071
                          · rcases h2bigk with h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [hlam, p1072_0]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [h1068, h3, h939, hc12, hlam, hphi, ht23, ht34, p1072_1, u4elo2]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [h3, hlam, p1072_0]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [h696, hlam, p1072_0]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [h1068, h1069, h1071, h3, h939, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1072_1, u4elo2]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [h0, hlam, p1072_1]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [hlam, p1072_0]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [h1060, hlam, p1072_0]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [h1062, hlam, p1072_0]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [h0, h1068, h1069, h1071, h3, h939, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1072_1, u4elo2]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              rcases p1072_3 (m.d 0 2) (by simp) with h1083 | h1083
                              · linarith only [h1083, hlam, p1072_0]
                              · rcases p1072_3 (m.d 1 2) (by simp) with h1085 | h1085
                                · linarith only [h1060, h1085, hlam]
                                · rcases p1072_3 (m.d 2 3) (by simp) with h1087 | h1087
                                  · rcases p1072_3 (m.d 2 4) (by simp) with h1088 | h1088
                                    · linarith only [h1068, h1088, hlam]
                                    · linarith only [h1088, h696, hlam]
                                  · linarith only [h1087, hlam, p1072_0]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              rcases p1072_3 (m.d 0 2) (by simp) with h1092 | h1092
                              · linarith only [h1092, h3, hlam]
                              · linarith only [h0, h1092, hlam]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [hlam, p1072_0]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [h1068, h3, h939, hc02, hc23, hlam, hphi, p1072_1]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [h1068, h3, h938, h939, hlam, p1072_2]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [h1069, h1071, h938, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1072_1, u4elo2]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, p1072_1, u4elo2]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [h1068, hlam, p1072_0]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [hlam, p1072_0]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              rcases p1072_3 (m.d 0 2) (by simp) with h1102 | h1102
                              · linarith only [h1102, h696, hlam]
                              · linarith only [h1102, h938, hlam]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [h938, hlam, p1072_0]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [h1068, h3, h938, h939, hc12, hc23, hlam, hphi, p1072_1]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [h1069, hlam, p1072_0]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [h1070, hlam, p1072_1]
                            · have p1072_0 := h1072c.1
                              have p1072_1 := h1072c.2.1
                              have p1072_2 := h1072c.2.2.1
                              have p1072_3 := h1072c.2.2.2
                              linarith only [hlam, p1072_0]
                          · linarith only [h1071, h3, h939, hc02, hlam, hphi, ht23, ht34, u4elo4]
                        · linarith only [h1067, h1068, h1070, h2, h3, h939, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h1, h1066, h1068, h1069, h939, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h1068, h3, h938, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                  · linarith only [h1059, h1067, h696, h938, hc14, hlam, hphi, u4elo2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1115 | h1115
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1116 | h1116
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1117 | h1117
                      · linarith only [h1066, h1116, h1117, h3, h938, h939, hc13, hlam, hphi, ht34, u4elo2]
                      · linarith only [h1116, h1117, h3, h939, hc02, hc35, hlam, hphi, ht23]
                    · linarith only [h1116, h3, h938, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                  · linarith only [h1059, h1060, h1064, h1115, h939, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · linarith only [h1059, h696, h938, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1123 | h1123
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1124 | h1124
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1125 | h1125
          · linarith only [h0, h1125, h3, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1127 | h1127
            · linarith only [h0, h1127, h696, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1129 | h1129
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1130 | h1130
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1131 | h1131
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1132 | h1132
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1133 | h1133
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1134 | h1134
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1135 | h1135
                          · rcases h2bigk with h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1134, h938, hc12, hc24, hlam, hphi, p1136_1]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h3, hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h696, hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h938, hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h0, hlam, p1136_1]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1125, hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1127, hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h0, h938, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1136_1]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              rcases p1136_3 (m.d 0 2) (by simp) with h1147 | h1147
                              · linarith only [h1147, hlam, p1136_0]
                              · rcases p1136_3 (m.d 1 2) (by simp) with h1149 | h1149
                                · linarith only [h1125, h1149, hlam]
                                · rcases p1136_3 (m.d 2 3) (by simp) with h1151 | h1151
                                  · rcases p1136_3 (m.d 2 4) (by simp) with h1152 | h1152
                                    · linarith only [h1132, h1152, hlam]
                                    · linarith only [h1152, h696, hlam]
                                  · linarith only [h1151, hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              rcases p1136_3 (m.d 0 2) (by simp) with h1156 | h1156
                              · linarith only [h1156, h3, hlam]
                              · linarith only [h0, h1156, hlam]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h0, h696, hc12, hc23, hlam, hphi, p1136_1]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h0, h938, hc12, hc23, hlam, hphi, p1136_1]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, p1136_1, u4elo2]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, p1136_1, u4elo2]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1132, hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h0, h938, hc12, hlam, hphi, ht23, ht34, p1136_1, u4elo2]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h0, h1134, hc12, hlam, hphi, ht23, ht34, p1136_1, u4elo2]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1134, hc12, hlam, hphi, ht23, ht34, p1136_1, u4elo2]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1133, hlam, p1136_0]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [h1134, hlam, p1136_1]
                            · have p1136_0 := h1136c.1
                              have p1136_1 := h1136c.2.1
                              have p1136_2 := h1136c.2.2.1
                              have p1136_3 := h1136c.2.2.2
                              linarith only [hlam, p1136_0]
                          · linarith only [h1124, h1135, hc34, hlam, hphi, u4elo0]
                        · linarith only [h0, h1134, h696, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h0, h1, h1130, h1133, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h1132, h3, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h1124, h1129, h1131, h696, hc34, hlam, hphi, u4elo2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1177 | h1177
                  · linarith only [h1129, h1130, h1177, hlam]
                  · linarith only [h1124, h1177, h696, hc14, hlam, hphi, u4elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1180 | h1180
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1181 | h1181
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1182 | h1182
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1183 | h1183
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1184 | h1184
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1185 | h1185
                          · rcases h2bigk with h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c | h1186c
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [hlam, p1186_0]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [h3, hc12, hc23, hlam, hphi, p1186_1]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [h3, hlam, p1186_0]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [h696, hlam, p1186_0]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [h938, hlam, p1186_0]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [h0, hlam, p1186_1]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [hlam, p1186_0]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [h1125, hlam, p1186_0]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [h1127, hlam, p1186_0]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [h0, h1123, h1129, h1180, h1185, h696, h938, hc01, hc02, hc45, hlam, hphi, ht0b, ht23, ht34, ht5b, p1186_1, u4elo2]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              rcases p1186_3 (m.d 0 2) (by simp) with h1197 | h1197
                              · linarith only [h1197, hlam, p1186_0]
                              · rcases p1186_3 (m.d 1 2) (by simp) with h1199 | h1199
                                · linarith only [h1125, h1199, hlam]
                                · rcases p1186_3 (m.d 2 3) (by simp) with h1201 | h1201
                                  · rcases p1186_3 (m.d 2 4) (by simp) with h1202 | h1202
                                    · linarith only [h1182, h1202, hlam]
                                    · linarith only [h1202, h696, hlam]
                                  · linarith only [h1201, hlam, p1186_0]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              rcases p1186_3 (m.d 0 2) (by simp) with h1206 | h1206
                              · linarith only [h1206, h3, hlam]
                              · linarith only [h0, h1206, hlam]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [hlam, p1186_0]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [h1123, h1129, h1180, h1185, h696, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1186_1]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [h0, h938, hc12, hc23, hlam, hphi, p1186_1]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, p1186_1, u4elo2]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, p1186_1, u4elo2]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [h1182, hlam, p1186_0]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [hlam, p1186_0]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [h0, h938, hc12, hlam, hphi, ht23, ht34, p1186_1, u4elo2]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [h0, h1184, hc12, hlam, hphi, ht23, ht34, p1186_1, u4elo2]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [h1184, hc12, hlam, hphi, ht23, ht34, p1186_1, u4elo2]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [h1183, hlam, p1186_0]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [h1184, hlam, p1186_1]
                            · have p1186_0 := h1186c.1
                              have p1186_1 := h1186c.2.1
                              have p1186_2 := h1186c.2.2.1
                              have p1186_3 := h1186c.2.2.2
                              linarith only [hlam, p1186_0]
                          · linarith only [h1129, h1180, h1185, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h1123, h1129, h1180, h1181, h1184, hc24, hlam, hphi, u4elo0]
                      · linarith only [h1123, h1129, h1183, h3, hc13, hc35, hlam, hphi]
                    · linarith only [h1123, h1182, h3, hlam]
                  · linarith only [h1124, h1181, hc14, hlam, hphi, u4elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1227 | h1227
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1228 | h1228
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1229 | h1229
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1230 | h1230
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1231 | h1231
                          · rcases h2bigk with h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [hlam, p1232_0]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [h3, hc12, hc23, hlam, hphi, p1232_1]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [h3, hlam, p1232_0]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [h696, hlam, p1232_0]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [h938, hlam, p1232_0]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [h0, hlam, p1232_1]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [hlam, p1232_0]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [h1125, hlam, p1232_0]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [h1127, hlam, p1232_0]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [h0, h938, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1232_1]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              rcases p1232_3 (m.d 0 2) (by simp) with h1243 | h1243
                              · linarith only [h1243, hlam, p1232_0]
                              · rcases p1232_3 (m.d 1 2) (by simp) with h1245 | h1245
                                · linarith only [h1125, h1245, hlam]
                                · rcases p1232_3 (m.d 2 3) (by simp) with h1247 | h1247
                                  · rcases p1232_3 (m.d 2 4) (by simp) with h1248 | h1248
                                    · linarith only [h1228, h1248, hlam]
                                    · linarith only [h1248, h696, hlam]
                                  · linarith only [h1247, hlam, p1232_0]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              rcases p1232_3 (m.d 0 2) (by simp) with h1252 | h1252
                              · linarith only [h1252, h3, hlam]
                              · linarith only [h0, h1252, hlam]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [hlam, p1232_0]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [h1123, h1125, h1180, h1231, h696, hc12, hc23, hlam, hphi, p1232_1]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [h1125, h1180, h1229, hc12, hc23, hlam, hphi, p1232_1]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, p1232_1, u4elo2]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, p1232_1, u4elo2]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [h1228, hlam, p1232_0]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [hlam, p1232_0]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [h1125, h1180, h1229, hc12, hlam, hphi, ht23, ht34, p1232_1, u4elo2]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [h0, h1230, hc12, hlam, hphi, ht23, ht34, p1232_1, u4elo2]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [h1230, hc12, hlam, hphi, ht23, ht34, p1232_1, u4elo2]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [h1229, hlam, p1232_0]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [h1230, hlam, p1232_1]
                            · have p1232_0 := h1232c.1
                              have p1232_1 := h1232c.2.1
                              have p1232_2 := h1232c.2.2.1
                              have p1232_3 := h1232c.2.2.2
                              linarith only [hlam, p1232_0]
                          · linarith only [h1227, h1231, hc34, hlam, hphi, u4elo1]
                        · linarith only [h1123, h1129, h1227, h1230, h696, hlam]
                      · linarith only [h1123, h1125, h1129, h1229, h3, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h1123, h1228, h3, hlam]
                  · linarith only [h1124, h1227, h696, hc14, hlam, hphi, u4elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1273 | h1273
          · linarith only [h0, h1123, h1273, h3, h696, hc34, hlam, hphi, u4elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1275 | h1275
            · linarith only [h0, h1124, h1275, h696, hc24, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1277 | h1277
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1278 | h1278
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1279 | h1279
                  · linarith only [h1124, h1279, h696, hc02, hlam, hphi, ht23, ht34, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1281 | h1281
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1282 | h1282
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1283 | h1283
                        · linarith only [h0, h1124, h1283, h696, hc12, hlam, hphi, ht23, ht34, u4elo2]
                        · linarith only [h0, h1283, h696, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h0, h1, h1278, h1281, h1282, h696, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h1281, h3, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1288 | h1288
                  · linarith only [h1124, h1288, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1290 | h1290
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1291 | h1291
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1292 | h1292
                        · linarith only [h0, h1124, h1292, h696, hc12, hlam, hphi, ht23, ht34, u4elo2]
                        · linarith only [h0, h1292, h696, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1295 | h1295
                        · linarith only [h0, h1124, h1290, h1291, h1295, h696, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1295, h696, hc12, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h1, h1277, h1290, h3, hlam]
              · linarith only [h1123, h1124, h1277, hc13, hlam, hphi, ht34, u4elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1300 | h1300
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1301 | h1301
          · linarith only [h0, h1301, h3, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1303 | h1303
            · linarith only [h0, h1123, h1303, h3, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1305 | h1305
              · linarith only [h1, h1123, h1305, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1307 | h1307
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1308 | h1308
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1309 | h1309
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1310 | h1310
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1311 | h1311
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1312 | h1312
                          · rcases h2bigk with h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c | h1313c
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [hlam, p1313_0]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [h3, hc12, hc23, hlam, hphi, p1313_1]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [h3, hlam, p1313_0]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [h696, hlam, p1313_0]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [h938, hlam, p1313_0]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [h0, hlam, p1313_1]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [hlam, p1313_0]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [h1301, hlam, p1313_0]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [h1303, hlam, p1313_0]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [h0, h696, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1313_1, u4elo2]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              rcases p1313_3 (m.d 0 2) (by simp) with h1324 | h1324
                              · linarith only [h1324, hlam, p1313_0]
                              · rcases p1313_3 (m.d 1 2) (by simp) with h1326 | h1326
                                · linarith only [h1301, h1326, hlam]
                                · rcases p1313_3 (m.d 2 3) (by simp) with h1328 | h1328
                                  · rcases p1313_3 (m.d 2 4) (by simp) with h1329 | h1329
                                    · linarith only [h1309, h1329, hlam]
                                    · linarith only [h1329, h696, hlam]
                                  · linarith only [h1328, hlam, p1313_0]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              rcases p1313_3 (m.d 0 2) (by simp) with h1333 | h1333
                              · linarith only [h1333, h3, hlam]
                              · linarith only [h0, h1333, hlam]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [hlam, p1313_0]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [h1123, h1309, h3, hc02, hc23, hlam, hphi, p1313_1]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [h0, h938, hc12, hc23, hlam, hphi, p1313_1]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, p1313_1, u4elo2]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, p1313_1, u4elo2]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [h1309, hlam, p1313_0]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [hlam, p1313_0]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [h0, h938, hc12, hlam, hphi, ht23, ht34, p1313_1, u4elo2]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [h0, h1311, hc12, hlam, hphi, ht23, ht34, p1313_1, u4elo2]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [h1311, hc12, hlam, hphi, ht23, ht34, p1313_1, u4elo2]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [h1310, hlam, p1313_0]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [h1311, hlam, p1313_1]
                            · have p1313_0 := h1313c.1
                              have p1313_1 := h1313c.2.1
                              have p1313_2 := h1313c.2.2.1
                              have p1313_3 := h1313c.2.2.2
                              linarith only [hlam, p1313_0]
                          · linarith only [h1, h1123, h1307, h1312, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h1308, h1311, h2, hc24, hlam, hphi, u4elo0]
                      · linarith only [h1, h1123, h1307, h1309, h1310, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h0, h1309, h3, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h1300, h1308, h696, hc14, hlam, hphi, u4elo2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1354 | h1354
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1355 | h1355
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1356 | h1356
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1357 | h1357
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1358 | h1358
                          · rcases h2bigk with h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [hlam, p1359_0]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [h3, hc12, hc23, hlam, hphi, p1359_1]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [h3, hlam, p1359_0]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [h696, hlam, p1359_0]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [h938, hlam, p1359_0]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [h0, hlam, p1359_1]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [hlam, p1359_0]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [h1301, hlam, p1359_0]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [h1303, hlam, p1359_0]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [h0, h696, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1359_1, u4elo2]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              rcases p1359_3 (m.d 0 2) (by simp) with h1370 | h1370
                              · linarith only [h1370, hlam, p1359_0]
                              · rcases p1359_3 (m.d 1 2) (by simp) with h1372 | h1372
                                · linarith only [h1301, h1372, hlam]
                                · rcases p1359_3 (m.d 2 3) (by simp) with h1374 | h1374
                                  · rcases p1359_3 (m.d 2 4) (by simp) with h1375 | h1375
                                    · linarith only [h1355, h1375, hlam]
                                    · linarith only [h1375, h696, hlam]
                                  · linarith only [h1374, hlam, p1359_0]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              rcases p1359_3 (m.d 0 2) (by simp) with h1379 | h1379
                              · linarith only [h1379, h3, hlam]
                              · linarith only [h0, h1379, hlam]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [hlam, p1359_0]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [h1123, h1355, h3, hc02, hc23, hlam, hphi, p1359_1]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [h0, h938, hc12, hc23, hlam, hphi, p1359_1]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, p1359_1, u4elo2]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, p1359_1, u4elo2]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [h1355, hlam, p1359_0]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [hlam, p1359_0]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [h1301, h1307, h1356, hc12, hlam, hphi, ht23, ht34, p1359_1, u4elo2]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [h0, h1357, hc12, hlam, hphi, ht23, ht34, p1359_1, u4elo2]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [h1357, hc12, hlam, hphi, ht23, ht34, p1359_1, u4elo2]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [h1356, hlam, p1359_0]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [h1357, hlam, p1359_1]
                            · have p1359_0 := h1359c.1
                              have p1359_1 := h1359c.2.1
                              have p1359_2 := h1359c.2.2.1
                              have p1359_3 := h1359c.2.2.2
                              linarith only [hlam, p1359_0]
                          · linarith only [h0, h1123, h1358, h3, hc12, hlam, hphi, ht23, ht34, u4elo4]
                        · linarith only [h1354, h1357, h2, hc24, hlam, hphi, u4elo0]
                      · linarith only [h1123, h1355, h1356, h3, hc02, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1355, h3, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h1300, h1354, h696, hc14, hlam, hphi, u4elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1400 | h1400
          · linarith only [h0, h1400, h3, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1402 | h1402
            · linarith only [h0, h1402, h696, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1404 | h1404
              · linarith only [h1, h1123, h1300, h1404, hc34, hlam, hphi, u4elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1406 | h1406
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1407 | h1407
                  · linarith only [h1123, h1300, h1407, h3, hc02, hlam, hphi, ht23, ht34, u4elo1]
                  · linarith only [h1404, h1406, h1407, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1410 | h1410
                  · linarith only [h1123, h1300, h1410, hc03, hlam, hphi, ht34, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1412 | h1412
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1413 | h1413
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1414 | h1414
                        · linarith only [h0, h1123, h1300, h1414, h3, hc12, hlam, hphi, ht23, ht34, u4elo2]
                        · linarith only [h0, h1414, h696, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h0, h1123, h1412, h1413, h3, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1412, h3, hc12, hlam, hphi, ht23, ht34, u4elo3]

set_option maxHeartbeats 7292000 in
set_option maxHeartbeats 7292000 in
theorem r1l7_12_24_L_I_M_LI_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact r1l7_12_24_L_I_M_LI_x0_x0_x0_x0 m hb2 hb4 h0 h1 h2 h3
  · exact r1l7_12_24_L_I_M_LI_x0_x0_x0_x1 m hb2 hb4 h0 h1 h2 h3

set_option maxHeartbeats 7292000 in
set_option maxHeartbeats 7292000 in
theorem r1l7_12_24_L_I_M_LI_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]

set_option maxHeartbeats 7292000 in
set_option maxHeartbeats 7292000 in
theorem r1l7_12_24_L_I_M_LI_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_12_24_L_I_M_LI_x0_x0_x0 m hb2 hb4 h0 h1 h2
  · exact r1l7_12_24_L_I_M_LI_x0_x0_x1 m hb2 hb4 h0 h1 h2

end R2N4
