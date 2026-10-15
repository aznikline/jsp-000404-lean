import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3494000 in
set_option maxHeartbeats 3494000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_R_M_IR_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h432 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h612 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h727 | h727
  · rcases m.htr 0 2 3 (by decide) (by decide) with h728 | h728
    · rcases m.htr 0 2 4 (by decide) (by decide) with h729 | h729
      · rcases m.htr 0 2 5 (by decide) (by decide) with h730 | h730
        · rcases m.htr 0 3 4 (by decide) (by decide) with h731 | h731
          · rcases m.htr 0 3 5 (by decide) (by decide) with h732 | h732
            · rcases m.htr 0 4 5 (by decide) (by decide) with h733 | h733
              · rcases m.htr 1 2 3 (by decide) (by decide) with h734 | h734
                · rcases m.htr 1 2 4 (by decide) (by decide) with h735 | h735
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h736 | h736
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h737 | h737
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h738 | h738
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h739 | h739
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h740 | h740
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h741 | h741
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h742 | h742
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h743 | h743
                                  · linarith only [h728, h740, h743, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h0, h729, h742, h743, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                                · linarith only [h612, h727, h734, h737, h739, h742, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                              · linarith only [h612, h727, h734, h737, h738, h741, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h748 | h748
                              · linarith only [h0, h728, h731, h740, h748, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                              · linarith only [h612, h727, h734, h737, h738, h748, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h612, h727, h739, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                        · linarith only [h612, h727, h737, h738, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h0, h432, h727, h728, h731, h736, h737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · linarith only [h0, h727, h736, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h432, h727, h734, h735, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h729, h734, hc23, hlam, hphi, u2ehi3]
              · linarith only [h612, h727, h733, hlam]
            · linarith only [h612, h727, h731, h732, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h759 | h759
            · rcases m.htr 0 4 5 (by decide) (by decide) with h760 | h760
              · rcases m.htr 1 2 3 (by decide) (by decide) with h761 | h761
                · rcases m.htr 1 2 4 (by decide) (by decide) with h762 | h762
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h763 | h763
                    · linarith only [h432, h727, h731, h763, hc34, hlam, hphi, ht23, u2ehi4]
                    · linarith only [h432, h727, h761, h763, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h432, h727, h761, h762, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h727, h728, h761, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
              · linarith only [h432, h727, h731, h760, hlam]
            · linarith only [h432, h727, h759, hlam]
        · linarith only [h728, h730, hc25, hlam, hphi, u2ehi2]
      · linarith only [h728, h729, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h772 | h772
      · linarith only [h728, h772, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h774 | h774
        · linarith only [h728, h774, hc23, hlam, hphi, u2ehi4]
        · linarith only [h0, h727, h774, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h777 | h777
    · rcases m.htr 0 2 4 (by decide) (by decide) with h778 | h778
      · rcases m.htr 0 2 5 (by decide) (by decide) with h779 | h779
        · rcases m.htr 0 3 4 (by decide) (by decide) with h780 | h780
          · rcases m.htr 0 3 5 (by decide) (by decide) with h781 | h781
            · rcases m.htr 0 4 5 (by decide) (by decide) with h782 | h782
              · rcases m.htr 1 2 3 (by decide) (by decide) with h783 | h783
                · rcases m.htr 1 2 4 (by decide) (by decide) with h784 | h784
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h785 | h785
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h786 | h786
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h787 | h787
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h788 | h788
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h789 | h789
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h790 | h790
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h791 | h791
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h792 | h792
                                  · linarith only [h777, h789, h792, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h0, h778, h791, h792, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h795 | h795
                                  · linarith only [h791, h795, hc34, hlam, hphi, ht23, u2ehi3]
                                  · rcases h1bigk with h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c | h797c
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [hlam, p797_0]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [h0, hlam, p797_0]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [h432, hlam, p797_0]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [h612, hlam, p797_0]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [h727, hlam, p797_0]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      rcases p797_3 (m.d 0 1) (by simp) with h803 | h803
                                      · linarith only [h803, hlam, p797_0]
                                      · rcases p797_3 (m.d 1 2) (by simp) with h805 | h805
                                        · rcases p797_3 (m.d 1 3) (by simp) with h806 | h806
                                          · linarith only [h783, h806, hlam]
                                          · linarith only [h432, h806, hlam]
                                        · linarith only [h805, hlam, p797_0]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [hlam, p797_0]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [h612, h782, h786, h791, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p797_1, u2ehi3]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [h612, h782, h791, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p797_1, u2ehi3]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [h727, hc01, hc12, hlam, hphi, p797_1]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      rcases p797_3 (m.d 0 1) (by simp) with h814 | h814
                                      · linarith only [h814, hlam, p797_0]
                                      · rcases p797_3 (m.d 1 2) (by simp) with h816 | h816
                                        · rcases p797_3 (m.d 1 3) (by simp) with h817 | h817
                                          · rcases p797_3 (m.d 1 4) (by simp) with h818 | h818
                                            · linarith only [h786, h818, hlam]
                                            · linarith only [h612, h818, hlam]
                                          · linarith only [h817, hlam, p797_0]
                                        · linarith only [h0, h816, hlam]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [h783, hlam, p797_0]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [hlam, p797_0]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [h612, h782, h791, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p797_1, u2ehi3]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [h727, h782, h783, h791, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p797_1, u2ehi3]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      rcases p797_3 (m.d 0 1) (by simp) with h827 | h827
                                      · linarith only [h827, hlam, p797_0]
                                      · rcases p797_3 (m.d 1 2) (by simp) with h829 | h829
                                        · rcases p797_3 (m.d 1 3) (by simp) with h830 | h830
                                          · rcases p797_3 (m.d 1 4) (by simp) with h831 | h831
                                            · rcases p797_3 (m.d 1 5) (by simp) with h832 | h832
                                              · linarith only [h788, h832, hlam]
                                              · linarith only [h727, h832, hlam]
                                            · linarith only [h831, hlam, p797_0]
                                          · linarith only [h432, h830, hlam]
                                        · linarith only [h0, h829, hlam]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [h784, hlam, p797_0]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [h786, hlam, p797_1]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [hlam, p797_0]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [h727, h782, h791, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p797_1, u2ehi3]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      rcases p797_3 (m.d 0 1) (by simp) with h842 | h842
                                      · linarith only [h842, hlam, p797_0]
                                      · rcases p797_3 (m.d 1 2) (by simp) with h844 | h844
                                        · rcases p797_3 (m.d 1 3) (by simp) with h845 | h845
                                          · rcases p797_3 (m.d 1 4) (by simp) with h846 | h846
                                            · rcases p797_3 (m.d 1 5) (by simp) with h847 | h847
                                              · rcases h5bigk with h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [hlam, p848_0]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [h727, hlam, p848_1]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  rcases p848_3 (m.d 0 5) (by simp) with h851 | h851
                                                  · rcases p848_3 (m.d 1 5) (by simp) with h852 | h852
                                                    · rcases p848_3 (m.d 2 5) (by simp) with h853 | h853
                                                      · linarith only [h779, h853, hlam]
                                                      · rcases p848_3 (m.d 3 5) (by simp) with h855 | h855
                                                        · linarith only [h781, h855, hlam]
                                                        · rcases p848_3 (m.d 4 5) (by simp) with h857 | h857
                                                          · linarith only [h782, h857, hlam]
                                                          · linarith only [h791, h857, hlam]
                                                    · linarith only [h785, h852, hlam]
                                                  · linarith only [h779, h851, hlam]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  rcases p848_3 (m.d 0 5) (by simp) with h862 | h862
                                                  · rcases p848_3 (m.d 1 5) (by simp) with h863 | h863
                                                    · rcases p848_3 (m.d 2 5) (by simp) with h864 | h864
                                                      · linarith only [h779, h864, hlam]
                                                      · linarith only [h790, h864, hlam]
                                                    · linarith only [h787, h863, hlam]
                                                  · linarith only [h781, h862, hlam]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [h612, h782, h783, h786, h791, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p848_1, u2ehi3]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [h782, h783, h786, h788, h791, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p848_1, u2ehi3]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [hlam, p848_0]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  rcases p848_3 (m.d 0 5) (by simp) with h872 | h872
                                                  · linarith only [h727, h872, hlam]
                                                  · linarith only [h779, h872, hlam]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  rcases p848_3 (m.d 0 5) (by simp) with h875 | h875
                                                  · linarith only [h727, h875, hlam]
                                                  · linarith only [h781, h875, hlam]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [h783, h786, h788, h791, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p848_1, u2ehi3]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [h779, hlam, p848_1]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [h785, hlam, p848_1]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [hlam, p848_0]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [h0, h779, h795, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p848_1, u4ehi3]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [h791, hlam, p848_0]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [h781, hlam, p848_1]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [h787, hlam, p848_1]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [h790, hlam, p848_0]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [hlam, p848_0]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [h795, hlam, p848_0]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [h782, hlam, p848_1]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [h788, hlam, p848_1]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [hc45, hlam, hphi, ht23, ht34, p848_1, u2ehi4]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [h612, h782, h783, h786, h795, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p848_1, u4ehi3]
                                                · have p848_0 := h848c.1
                                                  have p848_1 := h848c.2.1
                                                  have p848_2 := h848c.2.2.1
                                                  have p848_3 := h848c.2.2.2
                                                  linarith only [hlam, p848_0]
                                              · linarith only [h847, hlam, p797_0]
                                            · linarith only [h612, h846, hlam]
                                          · linarith only [h432, h845, hlam]
                                        · linarith only [h0, h844, hlam]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [h785, hlam, p797_0]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [h787, hlam, p797_0]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [h788, hlam, p797_0]
                                    · have p797_0 := h797c.1
                                      have p797_1 := h797c.2.1
                                      have p797_2 := h797c.2.2.1
                                      have p797_3 := h797c.2.2.2
                                      linarith only [hlam, p797_0]
                              · linarith only [h0, h777, h781, h789, h790, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h903 | h903
                              · linarith only [h0, h777, h780, h789, h903, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h905 | h905
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h906 | h906
                                  · rcases h1bigk with h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [hlam, p907_0]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [h0, hlam, p907_0]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [h432, hlam, p907_0]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [h612, hlam, p907_0]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [h727, hlam, p907_0]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      rcases p907_3 (m.d 0 1) (by simp) with h913 | h913
                                      · linarith only [h913, hlam, p907_0]
                                      · rcases p907_3 (m.d 1 2) (by simp) with h915 | h915
                                        · rcases p907_3 (m.d 1 3) (by simp) with h916 | h916
                                          · linarith only [h783, h916, hlam]
                                          · linarith only [h432, h916, hlam]
                                        · linarith only [h915, hlam, p907_0]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [hlam, p907_0]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [h432, hc01, hc12, hlam, hphi, p907_1]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [h612, hc01, hc12, hlam, hphi, p907_1]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [h727, h781, h903, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p907_1, u2ehi2]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      rcases p907_3 (m.d 0 1) (by simp) with h924 | h924
                                      · linarith only [h924, hlam, p907_0]
                                      · rcases p907_3 (m.d 1 2) (by simp) with h926 | h926
                                        · rcases p907_3 (m.d 1 3) (by simp) with h927 | h927
                                          · rcases p907_3 (m.d 1 4) (by simp) with h928 | h928
                                            · linarith only [h786, h928, hlam]
                                            · linarith only [h612, h928, hlam]
                                          · linarith only [h927, hlam, p907_0]
                                        · linarith only [h0, h926, hlam]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [h783, hlam, p907_0]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [hlam, p907_0]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [h727, h781, h788, h903, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p907_1, u2ehi2]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [h727, h781, h783, h903, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p907_1, u2ehi2]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      rcases p907_3 (m.d 0 1) (by simp) with h937 | h937
                                      · linarith only [h937, hlam, p907_0]
                                      · rcases p907_3 (m.d 1 2) (by simp) with h939 | h939
                                        · rcases p907_3 (m.d 1 3) (by simp) with h940 | h940
                                          · rcases p907_3 (m.d 1 4) (by simp) with h941 | h941
                                            · rcases p907_3 (m.d 1 5) (by simp) with h942 | h942
                                              · linarith only [h788, h942, hlam]
                                              · linarith only [h727, h942, hlam]
                                            · linarith only [h941, hlam, p907_0]
                                          · linarith only [h432, h940, hlam]
                                        · linarith only [h0, h939, hlam]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [h784, hlam, p907_0]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [h786, hlam, p907_1]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [hlam, p907_0]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [h727, h781, h903, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p907_1, u2ehi2]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      rcases p907_3 (m.d 0 1) (by simp) with h952 | h952
                                      · linarith only [h952, hlam, p907_0]
                                      · rcases p907_3 (m.d 1 2) (by simp) with h954 | h954
                                        · rcases p907_3 (m.d 1 3) (by simp) with h955 | h955
                                          · rcases p907_3 (m.d 1 4) (by simp) with h956 | h956
                                            · rcases p907_3 (m.d 1 5) (by simp) with h957 | h957
                                              · rcases h5bigk with h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [hlam, p958_0]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [h727, hlam, p958_1]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  rcases p958_3 (m.d 0 5) (by simp) with h961 | h961
                                                  · rcases p958_3 (m.d 1 5) (by simp) with h962 | h962
                                                    · rcases p958_3 (m.d 2 5) (by simp) with h963 | h963
                                                      · linarith only [h779, h963, hlam]
                                                      · rcases p958_3 (m.d 3 5) (by simp) with h965 | h965
                                                        · linarith only [h781, h965, hlam]
                                                        · linarith only [h903, h965, hlam]
                                                    · linarith only [h785, h962, hlam]
                                                  · linarith only [h779, h961, hlam]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [h903, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p958_1, u2ehi2]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  rcases p958_3 (m.d 0 5) (by simp) with h971 | h971
                                                  · rcases p958_3 (m.d 1 5) (by simp) with h972 | h972
                                                    · rcases p958_3 (m.d 2 5) (by simp) with h973 | h973
                                                      · linarith only [h779, h973, hlam]
                                                      · linarith only [h905, h973, hlam]
                                                    · linarith only [h788, h972, hlam]
                                                  · linarith only [h782, h971, hlam]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [h781, h783, h786, h788, h903, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p958_1, u2ehi2]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [hlam, p958_0]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  rcases p958_3 (m.d 0 5) (by simp) with h980 | h980
                                                  · linarith only [h727, h980, hlam]
                                                  · linarith only [h779, h980, hlam]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [h783, h786, h788, h903, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p958_1, u2ehi2]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  rcases p958_3 (m.d 0 5) (by simp) with h984 | h984
                                                  · linarith only [h727, h984, hlam]
                                                  · linarith only [h782, h984, hlam]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [h779, hlam, p958_1]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [h785, hlam, p958_1]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [hlam, p958_0]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [h903, hlam, p958_1]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [h0, h779, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p958_1, u4ehi4]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [h781, hlam, p958_1]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [h787, hlam, p958_1]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [hc35, hlam, hphi, ht23, p958_1, u2ehi4]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [hlam, p958_0]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [h0, h777, h780, h906, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p958_1, u4ehi4]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [h782, hlam, p958_1]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [h788, hlam, p958_1]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [h905, hlam, p958_1]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [h906, hlam, p958_1]
                                                · have p958_0 := h958c.1
                                                  have p958_1 := h958c.2.1
                                                  have p958_2 := h958c.2.2.1
                                                  have p958_3 := h958c.2.2.2
                                                  linarith only [hlam, p958_0]
                                              · linarith only [h957, hlam, p907_0]
                                            · linarith only [h612, h956, hlam]
                                          · linarith only [h432, h955, hlam]
                                        · linarith only [h0, h954, hlam]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [h785, hlam, p907_0]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [h787, hlam, p907_0]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [h788, hlam, p907_0]
                                    · have p907_0 := h907c.1
                                      have p907_1 := h907c.2.1
                                      have p907_2 := h907c.2.2.1
                                      have p907_3 := h907c.2.2.2
                                      linarith only [hlam, p907_0]
                                  · linarith only [h0, h778, h905, h906, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1011 | h1011
                                  · linarith only [h0, h1011, h777, h780, h789, h905, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                  · linarith only [h1011, h789, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h0, h612, h777, h780, h782, h788, hc01, hc12, hlam, hphi]
                        · linarith only [h432, h781, h787, hlam]
                      · linarith only [h432, h780, h786, hlam]
                    · linarith only [h0, h777, h785, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h0, h778, h784, hlam]
                · linarith only [h0, h777, h783, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1020 | h1020
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1021 | h1021
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1022 | h1022
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1023 | h1023
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1024 | h1024
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1025 | h1025
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1026 | h1026
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1027 | h1027
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1028 | h1028
                                · linarith only [h1028, h778, h782, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1030 | h1030
                                  · linarith only [h1026, h1030, h777, h778, h782, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · rcases h1bigk with h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [hlam, p1032_0]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [h0, hlam, p1032_0]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [h432, hlam, p1032_0]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [h612, hlam, p1032_0]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [h727, hlam, p1032_0]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      rcases p1032_3 (m.d 0 1) (by simp) with h1038 | h1038
                                      · linarith only [h1038, hlam, p1032_0]
                                      · rcases p1032_3 (m.d 1 2) (by simp) with h1040 | h1040
                                        · rcases p1032_3 (m.d 1 3) (by simp) with h1041 | h1041
                                          · linarith only [h1020, h1041, hlam]
                                          · linarith only [h1041, h432, hlam]
                                        · linarith only [h1040, hlam, p1032_0]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [hlam, p1032_0]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [h1023, h1025, h778, h782, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi3]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [h1025, h778, h782, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi3]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [h727, hc01, hc12, hlam, hphi, p1032_1]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      rcases p1032_3 (m.d 0 1) (by simp) with h1049 | h1049
                                      · linarith only [h1049, hlam, p1032_0]
                                      · rcases p1032_3 (m.d 1 2) (by simp) with h1051 | h1051
                                        · rcases p1032_3 (m.d 1 3) (by simp) with h1052 | h1052
                                          · rcases p1032_3 (m.d 1 4) (by simp) with h1053 | h1053
                                            · linarith only [h1023, h1053, hlam]
                                            · linarith only [h1053, h612, hlam]
                                          · linarith only [h1052, hlam, p1032_0]
                                        · linarith only [h0, h1051, hlam]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [h1020, hlam, p1032_0]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [hlam, p1032_0]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [h1025, h778, h782, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi3]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [h1020, h1025, h778, h782, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi3]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      rcases p1032_3 (m.d 0 1) (by simp) with h1062 | h1062
                                      · linarith only [h1062, hlam, p1032_0]
                                      · rcases p1032_3 (m.d 1 2) (by simp) with h1064 | h1064
                                        · rcases p1032_3 (m.d 1 3) (by simp) with h1065 | h1065
                                          · rcases p1032_3 (m.d 1 4) (by simp) with h1066 | h1066
                                            · rcases p1032_3 (m.d 1 5) (by simp) with h1067 | h1067
                                              · linarith only [h1025, h1067, hlam]
                                              · linarith only [h1067, h727, hlam]
                                            · linarith only [h1066, hlam, p1032_0]
                                          · linarith only [h1065, h432, hlam]
                                        · linarith only [h0, h1064, hlam]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [h1021, hlam, p1032_0]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [h1023, hlam, p1032_1]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [hlam, p1032_0]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [h1025, h778, h782, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi3]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      rcases p1032_3 (m.d 0 1) (by simp) with h1077 | h1077
                                      · linarith only [h1077, hlam, p1032_0]
                                      · rcases p1032_3 (m.d 1 2) (by simp) with h1079 | h1079
                                        · rcases p1032_3 (m.d 1 3) (by simp) with h1080 | h1080
                                          · rcases p1032_3 (m.d 1 4) (by simp) with h1081 | h1081
                                            · rcases p1032_3 (m.d 1 5) (by simp) with h1082 | h1082
                                              · rcases h5bigk with h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c | h1083c
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [hlam, p1083_0]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [h727, hlam, p1083_1]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [h782, hc45, hlam, hphi, ht23, ht34, p1083_1, u2ehi4]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [h1030, h782, hc45, hlam, hphi, p1083_1, u4ehi3]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [h782, hlam, p1083_0]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  rcases p1083_3 (m.d 0 5) (by simp) with h1089 | h1089
                                                  · linarith only [h1089, h727, hlam]
                                                  · rcases p1083_3 (m.d 1 5) (by simp) with h1091 | h1091
                                                    · rcases p1083_3 (m.d 2 5) (by simp) with h1092 | h1092
                                                      · linarith only [h1022, h1092, hlam]
                                                      · rcases p1083_3 (m.d 3 5) (by simp) with h1094 | h1094
                                                        · linarith only [h1024, h1094, hlam]
                                                        · rcases p1083_3 (m.d 4 5) (by simp) with h1096 | h1096
                                                          · linarith only [h1025, h1096, hlam]
                                                          · linarith only [h1096, h782, hlam]
                                                    · linarith only [h1091, h727, hlam]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [hlam, p1083_0]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  rcases p1083_3 (m.d 0 5) (by simp) with h1101 | h1101
                                                  · linarith only [h1101, h727, hlam]
                                                  · linarith only [h1101, h779, hlam]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  rcases p1083_3 (m.d 0 5) (by simp) with h1104 | h1104
                                                  · linarith only [h1104, h727, hlam]
                                                  · linarith only [h1104, h781, hlam]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [h1020, h1023, h1025, h778, h782, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1083_1, u2ehi3]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [h779, hlam, p1083_1]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [h1022, hlam, p1083_1]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [hlam, p1083_0]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [h0, h1030, h779, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1083_1, u4ehi3]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [h1028, hlam, p1083_0]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [h781, hlam, p1083_1]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [h1024, hlam, p1083_1]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [h1027, hlam, p1083_0]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [hlam, p1083_0]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [h1030, hlam, p1083_0]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [h779, hc45, hlam, hphi, ht23, ht34, p1083_1, u2ehi4]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [h1025, hlam, p1083_1]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [h1020, h1023, h1025, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1083_1, u2ehi4]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [h1020, h1023, h1025, h1030, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1083_1, u4ehi3]
                                                · have p1083_0 := h1083c.1
                                                  have p1083_1 := h1083c.2.1
                                                  have p1083_2 := h1083c.2.2.1
                                                  have p1083_3 := h1083c.2.2.2
                                                  linarith only [hlam, p1083_0]
                                              · linarith only [h1082, hlam, p1032_0]
                                            · linarith only [h1081, h612, hlam]
                                          · linarith only [h1080, h432, hlam]
                                        · linarith only [h0, h1079, hlam]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [h1022, hlam, p1032_0]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [h1024, hlam, p1032_0]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [h1025, hlam, p1032_0]
                                    · have p1032_0 := h1032c.1
                                      have p1032_1 := h1032c.2.1
                                      have p1032_2 := h1032c.2.2.1
                                      have p1032_3 := h1032c.2.2.2
                                      linarith only [hlam, p1032_0]
                              · linarith only [h1020, h1023, h1025, h1026, h1027, h781, h782, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                            · linarith only [h1020, h1023, h1025, h1026, h780, h782, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1133 | h1133
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1134 | h1134
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1135 | h1135
                                · linarith only [h1025, h1135, h612, hc01, hc24, hlam, hphi, ht12]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1137 | h1137
                                  · linarith only [h1025, h1133, h1137, h612, h778, hc23, hlam, hphi, u2ehi3]
                                  · rcases h1bigk with h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [hlam, p1139_0]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [h0, hlam, p1139_0]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [h432, hlam, p1139_0]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [h612, hlam, p1139_0]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [h727, hlam, p1139_0]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      rcases p1139_3 (m.d 0 1) (by simp) with h1145 | h1145
                                      · linarith only [h1145, hlam, p1139_0]
                                      · rcases p1139_3 (m.d 1 2) (by simp) with h1147 | h1147
                                        · rcases p1139_3 (m.d 1 3) (by simp) with h1148 | h1148
                                          · linarith only [h1020, h1148, hlam]
                                          · linarith only [h1148, h432, hlam]
                                        · linarith only [h1147, hlam, p1139_0]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [hlam, p1139_0]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [h432, hc01, hc12, hlam, hphi, p1139_1]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [h612, hc01, hc12, hlam, hphi, p1139_1]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [h727, hc01, hc12, hlam, hphi, p1139_1]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      rcases p1139_3 (m.d 0 1) (by simp) with h1156 | h1156
                                      · linarith only [h1156, hlam, p1139_0]
                                      · rcases p1139_3 (m.d 1 2) (by simp) with h1158 | h1158
                                        · rcases p1139_3 (m.d 1 3) (by simp) with h1159 | h1159
                                          · rcases p1139_3 (m.d 1 4) (by simp) with h1160 | h1160
                                            · linarith only [h1023, h1160, hlam]
                                            · linarith only [h1160, h612, hlam]
                                          · linarith only [h1159, hlam, p1139_0]
                                        · linarith only [h0, h1158, hlam]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [h1020, hlam, p1139_0]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [hlam, p1139_0]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [h612, hc01, hc13, hlam, hphi, p1139_1]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [h1020, h727, hc01, hc12, hlam, hphi, p1139_1]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [h1025, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1139_1]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [h1021, hlam, p1139_0]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [h1023, hlam, p1139_1]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [hlam, p1139_0]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [h1025, hlam, p1139_1]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      rcases p1139_3 (m.d 0 1) (by simp) with h1174 | h1174
                                      · linarith only [h1174, hlam, p1139_0]
                                      · rcases p1139_3 (m.d 1 2) (by simp) with h1176 | h1176
                                        · rcases p1139_3 (m.d 1 3) (by simp) with h1177 | h1177
                                          · rcases p1139_3 (m.d 1 4) (by simp) with h1178 | h1178
                                            · linarith only [h1025, h1178, hlam]
                                            · linarith only [h1178, h612, hlam]
                                          · linarith only [h1177, h432, hlam]
                                        · linarith only [h0, h1176, hlam]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [h1022, hlam, p1139_0]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [h1024, hlam, p1139_0]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [h612, hc01, hc15, hlam, hphi, p1139_1]
                                    · have p1139_0 := h1139c.1
                                      have p1139_1 := h1139c.2.1
                                      have p1139_2 := h1139c.2.2.1
                                      have p1139_3 := h1139c.2.2.2
                                      linarith only [hlam, p1139_0]
                              · linarith only [h1020, h1133, h1134, h432, h781, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                            · linarith only [h1133, h780, h782, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h1024, h432, h781, hlam]
                      · linarith only [h1023, h432, h780, h781, h782, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                    · linarith only [h0, h1022, h777, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1021, h777, hc24, hlam, hphi, u2ehi2]
                · linarith only [h0, h1020, h777, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1194 | h1194
              · linarith only [h1194, h780, h781, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1196 | h1196
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1197 | h1197
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1198 | h1198
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1199 | h1199
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1200 | h1200
                        · linarith only [h1200, h780, h781, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1202 | h1202
                          · linarith only [h1194, h1199, h1200, h1202, h778, hc35, hlam, hphi, ht23, u2ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1204 | h1204
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1205 | h1205
                              · linarith only [h1200, h1205, h432, h777, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1207 | h1207
                                · linarith only [h1202, h1207, h612, hc01, hc24, hlam, hphi, ht12]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1209 | h1209
                                  · linarith only [h1200, h1202, h1204, h1209, h432, h612, h777, h778, hc35, hlam, hphi, ht23, u2ehi3]
                                  · linarith only [h1200, h1204, h1209, h432, h777, hc45, hlam, hphi, u4ehi3]
                            · linarith only [h1200, h1204, h432, h780, hc23, hc35, hlam, hphi]
                      · linarith only [h1199, h432, h780, hlam]
                    · linarith only [h0, h1198, h777, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1197, h779, hc24, hlam, hphi, u2ehi4]
                · linarith only [h0, h1196, h779, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1217 | h1217
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1218 | h1218
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1219 | h1219
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1220 | h1220
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1221 | h1221
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1222 | h1222
                      · linarith only [h1217, h1222, h780, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1224 | h1224
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1225 | h1225
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1226 | h1226
                            · linarith only [h1222, h1224, h1226, h777, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1228 | h1228
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1229 | h1229
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1230 | h1230
                                  · rcases h1bigk with h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h0, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h432, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h612, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h727, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      rcases p1231_3 (m.d 0 1) (by simp) with h1237 | h1237
                                      · linarith only [h1237, hlam, p1231_0]
                                      · rcases p1231_3 (m.d 1 2) (by simp) with h1239 | h1239
                                        · rcases p1231_3 (m.d 1 3) (by simp) with h1240 | h1240
                                          · linarith only [h1219, h1240, hlam]
                                          · linarith only [h1240, h432, hlam]
                                        · linarith only [h1239, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1228, h1230, h432, h777, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1231_1, u4ehi4]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h612, hc01, hc12, hlam, hphi, p1231_1]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h727, hc01, hc12, hlam, hphi, p1231_1]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1222, hc01, hc34, hlam, hphi, ht12, ht23, p1231_1]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1219, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1222, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1222, h727, h779, hc34, hlam, hphi, ht23, p1231_1, u2ehi4]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      rcases p1231_3 (m.d 0 1) (by simp) with h1253 | h1253
                                      · linarith only [h1253, hlam, p1231_0]
                                      · rcases p1231_3 (m.d 1 2) (by simp) with h1255 | h1255
                                        · rcases p1231_3 (m.d 1 3) (by simp) with h1256 | h1256
                                          · linarith only [h1222, h1256, hlam]
                                          · linarith only [h1256, h432, hlam]
                                        · linarith only [h0, h1255, hlam]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1220, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h432, hc01, hc14, hlam, hphi, p1231_1]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1222, h727, h779, hc34, hlam, hphi, ht23, p1231_1, u2ehi4]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1222, h1224, hc01, hc34, hlam, hphi, ht12, ht23, p1231_1]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1221, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1224, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1225, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [hlam, p1231_0]
                                  · linarith only [h1222, h1230, h432, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · linarith only [h1217, h1218, h1222, h1229, h432, hc34, hlam, hphi, ht23, u2ehi3]
                              · linarith only [h1217, h1222, h1228, h432, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h1217, h1218, h1222, h1225, h432, h612, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1217, h1224, h432, hlam]
                    · linarith only [h0, h1221, h777, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1220, h778, hlam]
                · linarith only [h0, h1219, h778, hc23, hlam, hphi, u2ehi3]
              · linarith only [h1217, h1218, h780, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1278 | h1278
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1279 | h1279
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1280 | h1280
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1281 | h1281
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1282 | h1282
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1283 | h1283
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1284 | h1284
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1285 | h1285
                            · linarith only [h0, h1285, h432, h777, h780, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1287 | h1287
                              · linarith only [h1217, h1287, h777, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1289 | h1289
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1290 | h1290
                                  · rcases h1bigk with h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [hlam, p1291_0]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [h0, hlam, p1291_0]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [h432, hlam, p1291_0]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [h612, hlam, p1291_0]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [h727, hlam, p1291_0]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      rcases p1291_3 (m.d 0 1) (by simp) with h1297 | h1297
                                      · linarith only [h1297, hlam, p1291_0]
                                      · rcases p1291_3 (m.d 1 2) (by simp) with h1299 | h1299
                                        · rcases p1291_3 (m.d 1 3) (by simp) with h1300 | h1300
                                          · linarith only [h1279, h1300, hlam]
                                          · linarith only [h1300, h432, hlam]
                                        · linarith only [h1299, hlam, p1291_0]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [hlam, p1291_0]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [h1217, h1282, h1290, h777, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1291_1, u2ehi2]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [h612, hc01, hc12, hlam, hphi, p1291_1]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [h1217, h1283, h777, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1291_1, u2ehi2]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      rcases p1291_3 (m.d 0 1) (by simp) with h1308 | h1308
                                      · linarith only [h1308, hlam, p1291_0]
                                      · rcases p1291_3 (m.d 1 2) (by simp) with h1310 | h1310
                                        · rcases p1291_3 (m.d 1 3) (by simp) with h1311 | h1311
                                          · rcases p1291_3 (m.d 1 4) (by simp) with h1312 | h1312
                                            · linarith only [h1282, h1312, hlam]
                                            · linarith only [h1312, h612, hlam]
                                          · linarith only [h1311, hlam, p1291_0]
                                        · linarith only [h0, h1310, hlam]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [h1279, hlam, p1291_0]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [hlam, p1291_0]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [h1217, h1282, h1290, h777, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1291_1, u2ehi2]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [h1217, h1279, h1283, h777, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1291_1, u2ehi2]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      rcases p1291_3 (m.d 0 1) (by simp) with h1321 | h1321
                                      · linarith only [h1321, hlam, p1291_0]
                                      · rcases p1291_3 (m.d 1 2) (by simp) with h1323 | h1323
                                        · rcases p1291_3 (m.d 1 3) (by simp) with h1324 | h1324
                                          · rcases p1291_3 (m.d 1 4) (by simp) with h1325 | h1325
                                            · rcases p1291_3 (m.d 1 5) (by simp) with h1326 | h1326
                                              · linarith only [h1284, h1326, hlam]
                                              · linarith only [h1326, h727, hlam]
                                            · linarith only [h1325, hlam, p1291_0]
                                          · linarith only [h1324, h432, hlam]
                                        · linarith only [h0, h1323, hlam]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [h1280, hlam, p1291_0]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [h1282, hlam, p1291_1]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [hlam, p1291_0]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [h1217, h1283, h777, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1291_1, u2ehi2]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      rcases p1291_3 (m.d 0 1) (by simp) with h1336 | h1336
                                      · linarith only [h1336, hlam, p1291_0]
                                      · rcases p1291_3 (m.d 1 2) (by simp) with h1338 | h1338
                                        · rcases p1291_3 (m.d 1 3) (by simp) with h1339 | h1339
                                          · rcases p1291_3 (m.d 1 4) (by simp) with h1340 | h1340
                                            · rcases p1291_3 (m.d 1 5) (by simp) with h1341 | h1341
                                              · rcases h5bigk with h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [hlam, p1342_0]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [h727, hlam, p1342_1]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [h1217, h1287, h1290, hc34, hlam, hphi, ht23, p1342_1, u2ehi2]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [h1217, hlam, p1342_0]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [h1217, h1279, h1282, h1290, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1342_1, u4ehi4]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  rcases p1342_3 (m.d 0 5) (by simp) with h1348 | h1348
                                                  · linarith only [h1348, h727, hlam]
                                                  · rcases p1342_3 (m.d 1 5) (by simp) with h1350 | h1350
                                                    · rcases p1342_3 (m.d 2 5) (by simp) with h1351 | h1351
                                                      · linarith only [h1281, h1351, hlam]
                                                      · rcases p1342_3 (m.d 3 5) (by simp) with h1353 | h1353
                                                        · linarith only [h1283, h1353, hlam]
                                                        · linarith only [h1217, h1353, hlam]
                                                    · linarith only [h1350, h727, hlam]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [hlam, p1342_0]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  rcases p1342_3 (m.d 0 5) (by simp) with h1358 | h1358
                                                  · linarith only [h1358, h727, hlam]
                                                  · linarith only [h1358, h779, hlam]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [h1217, h1279, h1282, h1284, h777, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1342_1, u2ehi2]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  rcases p1342_3 (m.d 0 5) (by simp) with h1362 | h1362
                                                  · linarith only [h1362, h727, hlam]
                                                  · linarith only [h1278, h1362, hlam]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [h779, hlam, p1342_1]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [h1281, hlam, p1342_1]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [hlam, p1342_0]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [h1287, hlam, p1342_1]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [h0, h779, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1342_1, u4ehi4]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [h1290, h779, hc34, hlam, hphi, ht23, p1342_1, u2ehi4]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [h1283, hlam, p1342_1]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [h1279, h1282, h1290, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1342_1, u2ehi4]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [hlam, p1342_0]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [h1279, h1282, h1290, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1342_1, u4ehi4]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [h1278, hlam, p1342_1]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [h1284, hlam, p1342_1]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [h1289, hlam, p1342_1]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [h1290, hlam, p1342_1]
                                                · have p1342_0 := h1342c.1
                                                  have p1342_1 := h1342c.2.1
                                                  have p1342_2 := h1342c.2.2.1
                                                  have p1342_3 := h1342c.2.2.2
                                                  linarith only [hlam, p1342_0]
                                              · linarith only [h1341, hlam, p1291_0]
                                            · linarith only [h1340, h612, hlam]
                                          · linarith only [h1339, h432, hlam]
                                        · linarith only [h0, h1338, hlam]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [h1281, hlam, p1291_0]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [h1283, hlam, p1291_0]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [h1284, hlam, p1291_0]
                                    · have p1291_0 := h1291c.1
                                      have p1291_1 := h1291c.2.1
                                      have p1291_2 := h1291c.2.2.1
                                      have p1291_3 := h1291c.2.2.2
                                      linarith only [hlam, p1291_0]
                                  · linarith only [h1290, h777, h780, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                · linarith only [h1278, h1279, h1282, h1289, h780, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h1278, h1279, h1282, h1284, h780, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                        · linarith only [h1282, h1283, h780, hc03, hc35, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1392 | h1392
                        · linarith only [h1217, h1282, h1392, h777, hc34, hlam, hphi, ht23, u2ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1394 | h1394
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1395 | h1395
                            · linarith only [h1282, h1395, h432, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1397 | h1397
                              · linarith only [h1217, h1397, h777, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1399 | h1399
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1400 | h1400
                                  · rcases h1bigk with h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h0, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h432, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h612, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h727, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      rcases p1401_3 (m.d 0 1) (by simp) with h1407 | h1407
                                      · linarith only [h1407, hlam, p1401_0]
                                      · rcases p1401_3 (m.d 1 2) (by simp) with h1409 | h1409
                                        · rcases p1401_3 (m.d 1 3) (by simp) with h1410 | h1410
                                          · linarith only [h1279, h1410, hlam]
                                          · linarith only [h1410, h432, hlam]
                                        · linarith only [h1409, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h432, hc01, hc12, hlam, hphi, p1401_1]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h612, hc01, hc12, hlam, hphi, p1401_1]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h727, hc01, hc12, hlam, hphi, p1401_1]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1282, hc01, hc34, hlam, hphi, ht12, ht23, p1401_1]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1279, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1282, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1392, hlam, p1401_1]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      rcases p1401_3 (m.d 0 1) (by simp) with h1423 | h1423
                                      · linarith only [h1423, hlam, p1401_0]
                                      · rcases p1401_3 (m.d 1 2) (by simp) with h1425 | h1425
                                        · rcases p1401_3 (m.d 1 3) (by simp) with h1426 | h1426
                                          · linarith only [h1282, h1426, hlam]
                                          · linarith only [h1426, h432, hlam]
                                        · linarith only [h0, h1425, hlam]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1280, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h432, hc01, hc14, hlam, hphi, p1401_1]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1217, h1282, h727, h777, hc34, hlam, hphi, ht23, p1401_1, u2ehi2]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      rcases p1401_3 (m.d 0 1) (by simp) with h1434 | h1434
                                      · linarith only [h1434, hlam, p1401_0]
                                      · rcases p1401_3 (m.d 1 2) (by simp) with h1436 | h1436
                                        · rcases p1401_3 (m.d 1 3) (by simp) with h1437 | h1437
                                          · linarith only [h1392, h1437, hlam]
                                          · linarith only [h1437, h432, hlam]
                                        · linarith only [h0, h1436, hlam]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1281, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h432, hc01, hc15, hlam, hphi, p1401_1]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1394, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [hlam, p1401_0]
                                  · linarith only [h1400, h777, h780, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                · linarith only [h1278, h1282, h1399, h612, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h1278, h1394, h612, hlam]
                    · linarith only [h0, h1281, h777, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1280, h779, hc24, hlam, hphi, u2ehi4]
                · linarith only [h0, h1279, h778, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1451 | h1451
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1452 | h1452
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1453 | h1453
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1454 | h1454
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1455 | h1455
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1456 | h1456
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1457 | h1457
                            · linarith only [h1278, h1451, h1454, h1456, h1457, h777, h780, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1459 | h1459
                              · linarith only [h1217, h1459, h777, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1461 | h1461
                                · linarith only [h1278, h1461, h777, h780, hc24, hlam, hphi, u2ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1463 | h1463
                                  · linarith only [h1278, h1463, h777, h780, hc34, hlam, hphi, ht23, u2ehi2]
                                  · linarith only [h1451, h1454, h1456, h1463, h777, h780, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h1454, h1456, h777, h780, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h1454, h1455, h777, h780, hc35, hlam, hphi, ht23, u2ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1468 | h1468
                        · linarith only [h1217, h1454, h1468, h777, hc34, hlam, hphi, ht23, u2ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1470 | h1470
                          · linarith only [h1278, h1454, h1470, h778, hc34, hlam, hphi, ht23, u2ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1472 | h1472
                            · linarith only [h1454, h1470, h1472, h432, h777, hc45, hlam, hphi, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1474 | h1474
                              · linarith only [h1217, h1474, h777, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1476 | h1476
                                · linarith only [h1454, h1470, h1476, h432, h777, hc24, hlam, hphi, u2ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1478 | h1478
                                  · linarith only [h1454, h1470, h1478, h432, h777, hc34, hlam, hphi, ht23, u2ehi2]
                                  · linarith only [h1478, h777, h780, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h1453, h777, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1452, h777, hc24, hlam, hphi, u2ehi2]
                · linarith only [h0, h1451, h777, hlam]
        · linarith only [h777, h779, hc25, hlam, hphi, u2ehi2]
      · linarith only [h777, h778, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1486 | h1486
      · linarith only [h1486, h777, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1488 | h1488
        · linarith only [h1488, h777, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1490 | h1490
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1491 | h1491
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1492 | h1492
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1493 | h1493
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1494 | h1494
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1495 | h1495
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1496 | h1496
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1497 | h1497
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1498 | h1498
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1499 | h1499
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1500 | h1500
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1501 | h1501
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1502 | h1502
                                  · linarith only [h1490, h1493, h1502, h777, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h1486, h1492, h1493, h1499, h1502, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                                · linarith only [h1486, h1492, h1501, hlam]
                              · linarith only [h1491, h1500, h777, hlam]
                            · linarith only [h1499, h777, hc34, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h1490, h1492, h1493, h1498, h777, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                        · linarith only [h1486, h1494, h1496, h1497, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1490, h1493, h1496, h777, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h1493, h1495, h777, hc25, hlam, hphi, u2ehi0]
                  · linarith only [h1493, h1494, h777, hc24, hlam, hphi, u2ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1513 | h1513
                  · linarith only [h1493, h1513, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1515 | h1515
                    · linarith only [h1493, h1515, hc23, hlam, hphi, u2ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1517 | h1517
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1518 | h1518
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1519 | h1519
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1520 | h1520
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1521 | h1521
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1522 | h1522
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1523 | h1523
                                  · rcases h1bigk with h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [hlam, p1524_0]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [h0, hlam, p1524_0]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [h432, hlam, p1524_0]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [h612, hlam, p1524_0]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [h727, hlam, p1524_0]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [h1493, hc01, hc23, hlam, hphi, ht12, p1524_1]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [hlam, p1524_0]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [h1493, hlam, p1524_1]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [h1513, hlam, p1524_1]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [h1515, hlam, p1524_1]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      rcases p1524_3 (m.d 0 1) (by simp) with h1535 | h1535
                                      · linarith only [h1535, hlam, p1524_0]
                                      · rcases p1524_3 (m.d 1 2) (by simp) with h1537 | h1537
                                        · linarith only [h1493, h1537, hlam]
                                        · linarith only [h0, h1537, hlam]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [h1493, hc23, hlam, hphi, p1524_1, u2ehi1]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [hlam, p1524_0]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [h1493, h612, hc01, hc23, hlam, hphi, ht12, p1524_1]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [h1493, h727, hc01, hc23, hlam, hphi, ht12, p1524_1]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      rcases p1524_3 (m.d 0 1) (by simp) with h1544 | h1544
                                      · linarith only [h1544, hlam, p1524_0]
                                      · rcases p1524_3 (m.d 1 2) (by simp) with h1546 | h1546
                                        · linarith only [h1513, h1546, hlam]
                                        · linarith only [h0, h1546, hlam]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [h0, hc01, hc14, hlam, hphi, p1524_1]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [h1517, hlam, p1524_1]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [hlam, p1524_0]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [h1488, h1513, h1520, h727, hc23, hlam, hphi, p1524_1, u2ehi0]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      rcases p1524_3 (m.d 0 1) (by simp) with h1553 | h1553
                                      · linarith only [h1553, hlam, p1524_0]
                                      · rcases p1524_3 (m.d 1 2) (by simp) with h1555 | h1555
                                        · linarith only [h1515, h1555, hlam]
                                        · linarith only [h0, h1555, hlam]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [h0, hc01, hc15, hlam, hphi, p1524_1]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [h1518, hlam, p1524_0]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [h1519, hlam, p1524_0]
                                    · have p1524_0 := h1524c.1
                                      have p1524_1 := h1524c.2.1
                                      have p1524_2 := h1524c.2.2.1
                                      have p1524_3 := h1524c.2.2.2
                                      linarith only [hlam, p1524_0]
                                  · rcases h1bigk with h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [hlam, p1562_0]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [h0, hlam, p1562_0]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [h432, hlam, p1562_0]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [h612, hlam, p1562_0]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [h727, hlam, p1562_0]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [h1493, hc01, hc23, hlam, hphi, ht12, p1562_1]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [hlam, p1562_0]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [h1493, hlam, p1562_1]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [h1513, hlam, p1562_1]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [h1515, hlam, p1562_1]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      rcases p1562_3 (m.d 0 1) (by simp) with h1573 | h1573
                                      · linarith only [h1573, hlam, p1562_0]
                                      · rcases p1562_3 (m.d 1 2) (by simp) with h1575 | h1575
                                        · linarith only [h1493, h1575, hlam]
                                        · linarith only [h0, h1575, hlam]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [h1493, hc23, hlam, hphi, p1562_1, u2ehi1]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [hlam, p1562_0]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [h1493, h612, hc01, hc23, hlam, hphi, ht12, p1562_1]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [h1493, h727, hc01, hc23, hlam, hphi, ht12, p1562_1]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      rcases p1562_3 (m.d 0 1) (by simp) with h1582 | h1582
                                      · linarith only [h1582, hlam, p1562_0]
                                      · rcases p1562_3 (m.d 1 2) (by simp) with h1584 | h1584
                                        · linarith only [h1513, h1584, hlam]
                                        · linarith only [h0, h1584, hlam]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [h0, hc01, hc14, hlam, hphi, p1562_1]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [h1517, hlam, p1562_1]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [hlam, p1562_0]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [h1492, h1513, h1520, h1523, h727, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1562_1, u4ehi3]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      rcases p1562_3 (m.d 0 1) (by simp) with h1591 | h1591
                                      · linarith only [h1591, hlam, p1562_0]
                                      · rcases p1562_3 (m.d 1 2) (by simp) with h1593 | h1593
                                        · linarith only [h1515, h1593, hlam]
                                        · linarith only [h0, h1593, hlam]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [h0, hc01, hc15, hlam, hphi, p1562_1]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [h1518, hlam, p1562_0]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [h1519, hlam, p1562_0]
                                    · have p1562_0 := h1562c.1
                                      have p1562_1 := h1562c.2.1
                                      have p1562_2 := h1562c.2.2.1
                                      have p1562_3 := h1562c.2.2.2
                                      linarith only [hlam, p1562_0]
                                · linarith only [h1486, h1522, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                              · linarith only [h1491, h1493, h1521, h432, hlam]
                            · linarith only [h1520, h777, hc34, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h1492, h1519, h612, hlam]
                        · linarith only [h1491, h1518, h432, hlam]
                      · linarith only [h1490, h1517, h432, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1606 | h1606
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1607 | h1607
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1608 | h1608
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1609 | h1609
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1610 | h1610
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1611 | h1611
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1612 | h1612
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1613 | h1613
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1614 | h1614
                                · linarith only [h1486, h1492, h1614, hc24, hlam, hphi, u2ehi0]
                                · linarith only [h1486, h1609, h1611, h1614, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · linarith only [h1491, h1613, h777, hlam]
                            · linarith only [h1612, h777, hc34, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h1486, h1607, h1611, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h1486, h1607, h1609, h1610, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1490, h1609, h432, hlam]
                    · linarith only [h1606, h1608, h777, hc25, hlam, hphi, u2ehi0]
                  · linarith only [h1606, h1607, h777, hc24, hlam, hphi, u2ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1624 | h1624
                  · linarith only [h1606, h1624, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1626 | h1626
                    · linarith only [h1606, h1626, hc23, hlam, hphi, u2ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1628 | h1628
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1629 | h1629
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1630 | h1630
                          · linarith only [h1486, h1492, h1624, h1630, hc24, hlam, hphi, u2ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1632 | h1632
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1633 | h1633
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1634 | h1634
                                · linarith only [h1630, h1632, h1634, h612, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h1486, h1634, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                              · linarith only [h1633, h777, hc35, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h1490, h1606, h1632, h432, hlam]
                        · linarith only [h1491, h1629, h432, hlam]
                      · linarith only [h1490, h1491, h1492, h1628, h432, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1641 | h1641
              · linarith only [h1490, h1491, h1641, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1643 | h1643
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1644 | h1644
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1645 | h1645
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1646 | h1646
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1647 | h1647
                        · linarith only [h1490, h1491, h1647, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h1643, h1647, h777, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1490, h1643, h1646, h777, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h1643, h1645, h777, hc25, hlam, hphi, u2ehi0]
                  · linarith only [h1643, h1644, h777, hc24, hlam, hphi, u2ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1653 | h1653
                  · linarith only [h1643, h1653, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1655 | h1655
                    · linarith only [h1643, h1655, hc23, hlam, hphi, u2ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1657 | h1657
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1658 | h1658
                        · linarith only [h1490, h1491, h1658, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1660 | h1660
                          · linarith only [h1641, h1657, h1658, h1660, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1662 | h1662
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1663 | h1663
                              · linarith only [h1490, h1658, h1663, h432, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                              · linarith only [h1663, h777, hc35, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h1490, h1643, h1662, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                      · linarith only [h1490, h1491, h1657, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1668 | h1668
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1669 | h1669
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1670 | h1670
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1671 | h1671
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1672 | h1672
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1673 | h1673
                      · linarith only [h1490, h1668, h1673, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · linarith only [h1670, h1673, h777, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1671, h1672, hc25, hlam, hphi, u2ehi3]
                  · linarith only [h1670, h1671, h777, hc24, hlam, hphi, u2ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1678 | h1678
                  · linarith only [h1670, h1678, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1680 | h1680
                    · linarith only [h1670, h1680, hc23, hlam, hphi, u2ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1682 | h1682
                      · linarith only [h1490, h1668, h1682, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1684 | h1684
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1685 | h1685
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1686 | h1686
                            · linarith only [h1680, h1682, h1684, h1686, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h1686, h777, hc34, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h1669, h1685, h612, hlam]
                        · linarith only [h1668, h1684, h432, hlam]
              · linarith only [h1490, h1668, h1669, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1692 | h1692
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1693 | h1693
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1694 | h1694
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1695 | h1695
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1696 | h1696
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1697 | h1697
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1698 | h1698
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1699 | h1699
                            · linarith only [h1490, h1693, h1699, h777, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · linarith only [h1699, h777, hc34, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h1692, h1698, h612, hlam]
                        · linarith only [h1486, h1490, h1696, h1697, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1693, h1696, h777, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1693, h1695, h777, hc25, hlam, hphi, u2ehi0]
                  · linarith only [h1693, h1694, h777, hc24, hlam, hphi, u2ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1707 | h1707
                  · linarith only [h1693, h1707, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1709 | h1709
                    · linarith only [h1693, h1709, hc23, hlam, hphi, u2ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1711 | h1711
                      · linarith only [h1490, h1693, h1711, h777, hc23, hlam, hphi, u2ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1713 | h1713
                        · linarith only [h1668, h1711, h1713, h777, hc34, hlam, hphi, ht23, u2ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1715 | h1715
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1716 | h1716
                            · linarith only [h0, h1693, h1711, h1716, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h1716, h777, hc34, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h1692, h1715, h612, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1720 | h1720
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1721 | h1721
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1722 | h1722
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1723 | h1723
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1724 | h1724
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1725 | h1725
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1726 | h1726
                            · linarith only [h1490, h1720, h1726, h777, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · linarith only [h1726, h777, hc34, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h1486, h1721, h1725, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h1720, h1724, h777, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1720, h1723, h777, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1720, h1722, h777, hc25, hlam, hphi, u2ehi0]
                  · linarith only [h1720, h1721, h777, hc24, hlam, hphi, u2ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1734 | h1734
                  · linarith only [h1720, h1734, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1736 | h1736
                    · linarith only [h1720, h1736, hc23, hlam, hphi, u2ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1738 | h1738
                      · linarith only [h1490, h1720, h1738, h777, hc23, hlam, hphi, u2ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1740 | h1740
                        · linarith only [h1668, h1738, h1740, h777, hc34, hlam, hphi, ht23, u2ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1742 | h1742
                          · linarith only [h1490, h1692, h1734, h1742, h777, hc24, hlam, hphi, u2ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1744 | h1744
                            · linarith only [h1490, h1744, h777, hc23, hlam, hphi, u2ehi0]
                            · linarith only [h1744, h777, hc34, hlam, hphi, ht23, u2ehi0]

end R2N4
