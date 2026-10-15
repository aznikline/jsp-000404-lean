import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_8S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9890 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9891 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11319 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11320 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11321 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11322 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11323 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h11324 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  rcases m.htr 2 3 4 (by decide) (by decide) with h11729 | h11729
  · rcases m.htr 2 3 5 (by decide) (by decide) with h11730 | h11730
    · rcases m.htr 2 4 5 (by decide) (by decide) with h11731 | h11731
      · linarith only [h11324, h11731, h8836, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h11733 | h11733
        · linarith only [h11324, h11729, h11733, h8836, hc01, hc23, hlam, hphi, ht12]
        · rcases h0bigk with h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c | h11735c
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            linarith only [hlam, p11735_0]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            linarith only [h0, hlam, p11735_1]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            linarith only [h7600, hlam, p11735_0]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            linarith only [h8836, hlam, p11735_1]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            linarith only [h9666, hlam, p11735_1]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            rcases p11735_3 (m.d 0 1) (by simp) with h11741 | h11741
            · linarith only [h0, h11741, hlam]
            · rcases p11735_3 (m.d 0 2) (by simp) with h11743 | h11743
              · rcases p11735_3 (m.d 0 3) (by simp) with h11744 | h11744
                · linarith only [h11744, h9886, hlam]
                · linarith only [h11744, h7600, hlam]
              · linarith only [h0, h11743, hlam]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            linarith only [hlam, p11735_0]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            linarith only [h0, h9890, hc12, hlam, hphi, ht01, ht0b, ht5b, p11735_1, u5ehi3]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            rcases p11735_3 (m.d 0 1) (by simp) with h11750 | h11750
            · linarith only [h0, h11750, hlam]
            · rcases p11735_3 (m.d 0 2) (by simp) with h11752 | h11752
              · rcases p11735_3 (m.d 0 3) (by simp) with h11753 | h11753
                · linarith only [h11753, h9886, hlam]
                · linarith only [h11753, h9889, hlam]
              · linarith only [h11752, h9887, hlam]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            rcases p11735_3 (m.d 0 1) (by simp) with h11757 | h11757
            · linarith only [h0, h11757, hlam]
            · rcases p11735_3 (m.d 0 2) (by simp) with h11759 | h11759
              · rcases p11735_3 (m.d 0 3) (by simp) with h11760 | h11760
                · linarith only [h11760, h9886, hlam]
                · linarith only [h11760, h9890, hlam]
              · linarith only [h11759, h9888, hlam]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            rcases p11735_3 (m.d 0 1) (by simp) with h11764 | h11764
            · linarith only [h11764, h7600, hlam]
            · rcases p11735_3 (m.d 0 2) (by simp) with h11766 | h11766
              · rcases p11735_3 (m.d 0 3) (by simp) with h11767 | h11767
                · rcases p11735_3 (m.d 0 4) (by simp) with h11768 | h11768
                  · linarith only [h11768, h9889, hlam]
                  · linarith only [h11768, h8836, hlam]
                · linarith only [h11767, h7600, hlam]
              · linarith only [h0, h11766, hlam]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            linarith only [h9886, hlam, p11735_1]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            linarith only [hlam, p11735_0]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            rcases p11735_3 (m.d 0 1) (by simp) with h11775 | h11775
            · linarith only [h11775, h7600, hlam]
            · rcases p11735_3 (m.d 0 2) (by simp) with h11777 | h11777
              · rcases p11735_3 (m.d 0 3) (by simp) with h11778 | h11778
                · rcases p11735_3 (m.d 0 4) (by simp) with h11779 | h11779
                  · linarith only [h11779, h9889, hlam]
                  · rcases p11735_3 (m.d 0 5) (by simp) with h11781 | h11781
                    · linarith only [h11781, h9890, hlam]
                    · linarith only [h11781, h9891, hlam]
                · linarith only [h11778, h9889, hlam]
              · linarith only [h11777, h9887, hlam]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            rcases p11735_3 (m.d 0 1) (by simp) with h11786 | h11786
            · linarith only [h11786, h7600, hlam]
            · rcases p11735_3 (m.d 0 2) (by simp) with h11788 | h11788
              · rcases p11735_3 (m.d 0 3) (by simp) with h11789 | h11789
                · rcases p11735_3 (m.d 0 4) (by simp) with h11790 | h11790
                  · linarith only [h11790, h9889, hlam]
                  · rcases p11735_3 (m.d 0 5) (by simp) with h11792 | h11792
                    · linarith only [h11792, h9890, hlam]
                    · rcases h2bigk with h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c | h11794c
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [hlam, p11794_0]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [h0, hlam, p11794_1]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [h0, h11730, hc12, hlam, hphi, ht01, ht0b, ht5b, p11794_1, u5ehi3]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        rcases p11794_3 (m.d 0 2) (by simp) with h11798 | h11798
                        · rcases p11794_3 (m.d 1 2) (by simp) with h11799 | h11799
                          · rcases p11794_3 (m.d 2 3) (by simp) with h11800 | h11800
                            · linarith only [h11800, h9886, hlam]
                            · linarith only [h11729, h11800, hlam]
                          · linarith only [h11320, h11799, hlam]
                        · linarith only [h11798, hlam, p11794_0]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        rcases p11794_3 (m.d 0 2) (by simp) with h11805 | h11805
                        · rcases p11794_3 (m.d 1 2) (by simp) with h11806 | h11806
                          · rcases p11794_3 (m.d 2 3) (by simp) with h11807 | h11807
                            · linarith only [h11807, h9886, hlam]
                            · linarith only [h11730, h11807, hlam]
                          · linarith only [h11321, h11806, hlam]
                        · linarith only [h11805, hlam, p11794_0]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [h11730, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, p11794_1, u5ehi3]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [hlam, p11794_0]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [h11730, hc12, hlam, hphi, ht01, ht0b, ht5b, p11794_1, u5ehi3]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        rcases p11794_3 (m.d 0 2) (by simp) with h11815 | h11815
                        · linarith only [h0, h11815, hlam]
                        · linarith only [h11815, h9887, hlam]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        rcases p11794_3 (m.d 0 2) (by simp) with h11818 | h11818
                        · linarith only [h0, h11818, hlam]
                        · linarith only [h11818, h9888, hlam]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [h9886, hlam, p11794_0]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [h11319, hlam, p11794_0]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [hlam, p11794_0]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        rcases p11794_3 (m.d 0 2) (by simp) with h11824 | h11824
                        · rcases p11794_3 (m.d 1 2) (by simp) with h11825 | h11825
                          · rcases p11794_3 (m.d 2 3) (by simp) with h11826 | h11826
                            · rcases p11794_3 (m.d 2 4) (by simp) with h11827 | h11827
                              · linarith only [h11729, h11827, hlam]
                              · rcases p11794_3 (m.d 2 5) (by simp) with h11829 | h11829
                                · linarith only [h11730, h11829, hlam]
                                · linarith only [h11731, h11829, hlam]
                            · linarith only [h11729, h11826, hlam]
                          · linarith only [h11320, h11825, hlam]
                        · linarith only [h11824, h9887, hlam]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [h9886, hc02, hlam, hphi, ht0b, ht5b, p11794_1, u5ehi2]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [h9887, hlam, p11794_0]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [h11320, hlam, p11794_0]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [h11729, hlam, p11794_1]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [hlam, p11794_0]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [h11731, hlam, p11794_1]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [h9888, hlam, p11794_0]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [h11321, hlam, p11794_0]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [h11730, hlam, p11794_1]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [h11319, h11729, h7600, h9888, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11735_1, p11794_1]
                      · have p11794_0 := h11794c.1
                        have p11794_1 := h11794c.2.1
                        have p11794_2 := h11794c.2.2.1
                        have p11794_3 := h11794c.2.2.2
                        linarith only [hlam, p11794_0]
                · linarith only [h11789, h9890, hlam]
              · linarith only [h11788, h9888, hlam]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            linarith only [h11324, h8836, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11735_1]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            linarith only [h9887, hlam, p11735_0]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            linarith only [h9889, hlam, p11735_0]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            linarith only [hlam, p11735_0]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            linarith only [h9891, hlam, p11735_0]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            rcases p11735_3 (m.d 0 1) (by simp) with h11853 | h11853
            · linarith only [h11853, h9666, hlam]
            · rcases p11735_3 (m.d 0 2) (by simp) with h11855 | h11855
              · rcases p11735_3 (m.d 0 3) (by simp) with h11856 | h11856
                · rcases p11735_3 (m.d 0 4) (by simp) with h11857 | h11857
                  · linarith only [h11857, h9891, hlam]
                  · linarith only [h11857, h8836, hlam]
                · linarith only [h11856, h7600, hlam]
              · linarith only [h0, h11855, hlam]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            linarith only [h9888, hlam, p11735_1]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            linarith only [h9890, hlam, p11735_0]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            rcases p11735_3 (m.d 0 1) (by simp) with h11864 | h11864
            · linarith only [h11864, h9666, hlam]
            · rcases p11735_3 (m.d 0 2) (by simp) with h11866 | h11866
              · rcases p11735_3 (m.d 0 3) (by simp) with h11867 | h11867
                · rcases p11735_3 (m.d 0 4) (by simp) with h11868 | h11868
                  · linarith only [h11868, h9891, hlam]
                  · rcases p11735_3 (m.d 0 5) (by simp) with h11870 | h11870
                    · rcases h2bigk with h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c | h11871c
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [hlam, p11871_0]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [h0, hlam, p11871_1]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [h0, h11730, hc12, hlam, hphi, ht01, ht0b, ht5b, p11871_1, u5ehi3]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        rcases p11871_3 (m.d 0 2) (by simp) with h11875 | h11875
                        · rcases p11871_3 (m.d 1 2) (by simp) with h11876 | h11876
                          · rcases p11871_3 (m.d 2 3) (by simp) with h11877 | h11877
                            · linarith only [h11877, h9886, hlam]
                            · linarith only [h11729, h11877, hlam]
                          · linarith only [h11320, h11876, hlam]
                        · linarith only [h11875, hlam, p11871_0]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        rcases p11871_3 (m.d 0 2) (by simp) with h11882 | h11882
                        · rcases p11871_3 (m.d 1 2) (by simp) with h11883 | h11883
                          · rcases p11871_3 (m.d 2 3) (by simp) with h11884 | h11884
                            · linarith only [h11884, h9886, hlam]
                            · linarith only [h11730, h11884, hlam]
                          · linarith only [h11321, h11883, hlam]
                        · linarith only [h11882, hlam, p11871_0]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [h11730, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, p11871_1, u5ehi3]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [hlam, p11871_0]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [h11730, hc12, hlam, hphi, ht01, ht0b, ht5b, p11871_1, u5ehi3]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        rcases p11871_3 (m.d 0 2) (by simp) with h11892 | h11892
                        · linarith only [h0, h11892, hlam]
                        · linarith only [h11892, h9887, hlam]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        rcases p11871_3 (m.d 0 2) (by simp) with h11895 | h11895
                        · linarith only [h0, h11895, hlam]
                        · linarith only [h11895, h9888, hlam]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [h9886, hlam, p11871_0]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [h11319, hlam, p11871_0]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [hlam, p11871_0]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        rcases p11871_3 (m.d 0 2) (by simp) with h11901 | h11901
                        · rcases p11871_3 (m.d 1 2) (by simp) with h11902 | h11902
                          · rcases p11871_3 (m.d 2 3) (by simp) with h11903 | h11903
                            · rcases p11871_3 (m.d 2 4) (by simp) with h11904 | h11904
                              · linarith only [h11729, h11904, hlam]
                              · rcases p11871_3 (m.d 2 5) (by simp) with h11906 | h11906
                                · linarith only [h11730, h11906, hlam]
                                · linarith only [h11731, h11906, hlam]
                            · linarith only [h11729, h11903, hlam]
                          · linarith only [h11320, h11902, hlam]
                        · linarith only [h11901, h9887, hlam]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [h11730, h9886, hc02, hlam, hphi, ht0b, ht5b, p11871_1, u5ehi3]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [h9887, hlam, p11871_0]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [h11320, hlam, p11871_0]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [h11729, hlam, p11871_1]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [hlam, p11871_0]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [h11731, hlam, p11871_1]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [h9888, hlam, p11871_0]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [h11321, hlam, p11871_0]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [h11730, hlam, p11871_1]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        rcases p11871_3 (m.d 0 2) (by simp) with h11921 | h11921
                        · rcases p11871_3 (m.d 1 2) (by simp) with h11922 | h11922
                          · rcases p11871_3 (m.d 2 3) (by simp) with h11923 | h11923
                            · rcases p11871_3 (m.d 2 4) (by simp) with h11924 | h11924
                              · linarith only [h11731, h11924, hlam]
                              · rcases p11871_3 (m.d 2 5) (by simp) with h11926 | h11926
                                · rcases h3bigk with h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c | h11927c
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [hlam, p11927_0]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [h7600, hlam, p11927_1]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [h11729, h11730, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p11871_1, p11927_1]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    rcases p11927_3 (m.d 0 3) (by simp) with h11931 | h11931
                                    · rcases p11927_3 (m.d 1 3) (by simp) with h11932 | h11932
                                      · rcases p11927_3 (m.d 2 3) (by simp) with h11933 | h11933
                                        · linarith only [h11933, h9886, hlam]
                                        · linarith only [h11729, h11933, hlam]
                                      · linarith only [h11322, h11932, hlam]
                                    · linarith only [h11931, hlam, p11927_0]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    rcases p11927_3 (m.d 0 3) (by simp) with h11938 | h11938
                                    · rcases p11927_3 (m.d 1 3) (by simp) with h11939 | h11939
                                      · rcases p11927_3 (m.d 2 3) (by simp) with h11940 | h11940
                                        · linarith only [h11940, h9886, hlam]
                                        · linarith only [h11730, h11940, hlam]
                                      · linarith only [h11323, h11939, hlam]
                                    · linarith only [h11938, hlam, p11927_0]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [h11319, h11729, h11730, h9886, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11871_1, p11927_1]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [hlam, p11927_0]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [h11319, h11324, h11729, h11730, h8836, h9666, hc01, hc12, hc34, hc45, hlam, hphi, p11735_1, p11871_1, p11927_1]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    rcases p11927_3 (m.d 0 3) (by simp) with h11948 | h11948
                                    · linarith only [h11948, h7600, hlam]
                                    · linarith only [h11948, h9889, hlam]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    rcases p11927_3 (m.d 0 3) (by simp) with h11951 | h11951
                                    · linarith only [h11951, h7600, hlam]
                                    · linarith only [h11951, h9890, hlam]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [h9886, hlam, p11927_0]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [h11319, hlam, p11927_0]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [hlam, p11927_0]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    rcases p11927_3 (m.d 0 3) (by simp) with h11957 | h11957
                                    · rcases p11927_3 (m.d 1 3) (by simp) with h11958 | h11958
                                      · rcases p11927_3 (m.d 2 3) (by simp) with h11959 | h11959
                                        · rcases p11927_3 (m.d 3 4) (by simp) with h11960 | h11960
                                          · linarith only [h11960, hlam, p11927_0]
                                          · rcases p11927_3 (m.d 3 5) (by simp) with h11962 | h11962
                                            · linarith only [h11730, h11962, hlam]
                                            · linarith only [h11733, h11962, hlam]
                                        · linarith only [h11959, hlam, p11927_0]
                                      · linarith only [h11322, h11958, hlam]
                                    · linarith only [h11957, h9889, hlam]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [h0, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, p11927_1, u5ehi3]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [h9889, hlam, p11927_0]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [h11322, hlam, p11927_0]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [h11729, hlam, p11927_0]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [hlam, p11927_0]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [h11733, hlam, p11927_1]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [h9890, hlam, p11927_0]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [h11323, hlam, p11927_0]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [h11730, hlam, p11927_0]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [h0, h11324, h11730, h8836, h9666, h9886, hc01, hc12, hc34, hc45, hlam, hphi, p11735_1, p11927_1]
                                  · have p11927_0 := h11927c.1
                                    have p11927_1 := h11927c.2.1
                                    have p11927_2 := h11927c.2.2.1
                                    have p11927_3 := h11927c.2.2.2
                                    linarith only [hlam, p11927_0]
                                · linarith only [h11731, h11926, hlam]
                            · linarith only [h11729, h11923, hlam]
                          · linarith only [h11320, h11922, hlam]
                        · linarith only [h11921, h9887, hlam]
                      · have p11871_0 := h11871c.1
                        have p11871_1 := h11871c.2.1
                        have p11871_2 := h11871c.2.2.1
                        have p11871_3 := h11871c.2.2.2
                        linarith only [hlam, p11871_0]
                    · linarith only [h11870, h9891, hlam]
                · linarith only [h11867, h9889, hlam]
              · linarith only [h11866, h9887, hlam]
          · have p11735_0 := h11735c.1
            have p11735_1 := h11735c.2.1
            have p11735_2 := h11735c.2.2.1
            have p11735_3 := h11735c.2.2.2
            linarith only [hlam, p11735_0]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h11988 | h11988
      · linarith only [h11324, h11988, h8836, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h11990 | h11990
        · linarith only [h11324, h11990, h8836, hc01, hc34, hlam, hphi, ht12, ht23]
        · rcases h0bigk with h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c | h11992c
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [hlam, p11992_0]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [h0, hlam, p11992_1]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [h7600, hlam, p11992_0]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [h8836, hlam, p11992_1]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [h9666, hlam, p11992_1]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            rcases p11992_3 (m.d 0 1) (by simp) with h11998 | h11998
            · linarith only [h0, h11998, hlam]
            · rcases p11992_3 (m.d 0 2) (by simp) with h12000 | h12000
              · rcases p11992_3 (m.d 0 3) (by simp) with h12001 | h12001
                · linarith only [h12001, h9886, hlam]
                · linarith only [h12001, h7600, hlam]
              · linarith only [h0, h12000, hlam]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [hlam, p11992_0]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [h0, h11730, h9890, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11992_1]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            rcases p11992_3 (m.d 0 1) (by simp) with h12007 | h12007
            · linarith only [h0, h12007, hlam]
            · rcases p11992_3 (m.d 0 2) (by simp) with h12009 | h12009
              · rcases p11992_3 (m.d 0 3) (by simp) with h12010 | h12010
                · linarith only [h12010, h9886, hlam]
                · linarith only [h12010, h9889, hlam]
              · linarith only [h12009, h9887, hlam]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [h0, h11729, h11730, h9890, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11992_1]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            rcases p11992_3 (m.d 0 1) (by simp) with h12015 | h12015
            · linarith only [h12015, h7600, hlam]
            · rcases p11992_3 (m.d 0 2) (by simp) with h12017 | h12017
              · rcases p11992_3 (m.d 0 3) (by simp) with h12018 | h12018
                · rcases p11992_3 (m.d 0 4) (by simp) with h12019 | h12019
                  · linarith only [h12019, h9889, hlam]
                  · linarith only [h12019, h8836, hlam]
                · linarith only [h12018, h7600, hlam]
              · linarith only [h0, h12017, hlam]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [h9886, hlam, p11992_1]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [hlam, p11992_0]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            rcases p11992_3 (m.d 0 1) (by simp) with h12026 | h12026
            · linarith only [h12026, h7600, hlam]
            · rcases p11992_3 (m.d 0 2) (by simp) with h12028 | h12028
              · rcases p11992_3 (m.d 0 3) (by simp) with h12029 | h12029
                · rcases p11992_3 (m.d 0 4) (by simp) with h12030 | h12030
                  · linarith only [h12030, h9889, hlam]
                  · rcases p11992_3 (m.d 0 5) (by simp) with h12032 | h12032
                    · linarith only [h12032, h9890, hlam]
                    · linarith only [h12032, h9891, hlam]
                · linarith only [h12029, h9889, hlam]
              · linarith only [h12028, h9887, hlam]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [h11729, h11730, h9890, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p11992_1]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [h11324, h8836, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11992_1]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [h9887, hlam, p11992_0]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [h9889, hlam, p11992_0]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [hlam, p11992_0]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [h9891, hlam, p11992_0]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            rcases p11992_3 (m.d 0 1) (by simp) with h12043 | h12043
            · linarith only [h12043, h9666, hlam]
            · rcases p11992_3 (m.d 0 2) (by simp) with h12045 | h12045
              · rcases p11992_3 (m.d 0 3) (by simp) with h12046 | h12046
                · rcases p11992_3 (m.d 0 4) (by simp) with h12047 | h12047
                  · linarith only [h12047, h9891, hlam]
                  · linarith only [h12047, h8836, hlam]
                · linarith only [h12046, h7600, hlam]
              · linarith only [h0, h12045, hlam]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [h9888, hlam, p11992_1]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [h9890, hlam, p11992_0]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            rcases p11992_3 (m.d 0 1) (by simp) with h12054 | h12054
            · linarith only [h12054, h9666, hlam]
            · rcases p11992_3 (m.d 0 2) (by simp) with h12056 | h12056
              · rcases p11992_3 (m.d 0 3) (by simp) with h12057 | h12057
                · rcases p11992_3 (m.d 0 4) (by simp) with h12058 | h12058
                  · linarith only [h12058, h9891, hlam]
                  · rcases p11992_3 (m.d 0 5) (by simp) with h12060 | h12060
                    · rcases h2bigk with h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [hlam, p12061_0]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [h0, hlam, p12061_1]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        rcases p12061_3 (m.d 0 2) (by simp) with h12064 | h12064
                        · rcases p12061_3 (m.d 1 2) (by simp) with h12065 | h12065
                          · rcases p12061_3 (m.d 2 3) (by simp) with h12066 | h12066
                            · linarith only [h12066, hlam, p12061_0]
                            · rcases p12061_3 (m.d 2 4) (by simp) with h12068 | h12068
                              · linarith only [h12068, h9887, hlam]
                              · rcases p12061_3 (m.d 2 5) (by simp) with h12070 | h12070
                                · linarith only [h12070, h9888, hlam]
                                · linarith only [h11730, h12070, hlam]
                          · linarith only [h11319, h12065, hlam]
                        · linarith only [h12064, hlam, p12061_0]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        rcases p12061_3 (m.d 0 2) (by simp) with h12075 | h12075
                        · rcases p12061_3 (m.d 1 2) (by simp) with h12076 | h12076
                          · rcases p12061_3 (m.d 2 3) (by simp) with h12077 | h12077
                            · linarith only [h12077, h9886, hlam]
                            · linarith only [h11729, h12077, hlam]
                          · linarith only [h11320, h12076, hlam]
                        · linarith only [h12075, hlam, p12061_0]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        rcases p12061_3 (m.d 0 2) (by simp) with h12082 | h12082
                        · rcases p12061_3 (m.d 1 2) (by simp) with h12083 | h12083
                          · rcases p12061_3 (m.d 2 3) (by simp) with h12084 | h12084
                            · linarith only [h12084, h9886, hlam]
                            · rcases p12061_3 (m.d 2 4) (by simp) with h12086 | h12086
                              · linarith only [h12086, h9887, hlam]
                              · rcases p12061_3 (m.d 2 5) (by simp) with h12088 | h12088
                                · linarith only [h12088, hlam, p12061_0]
                                · rcases h3bigk with h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [hlam, p12090_0]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [h7600, hlam, p12090_1]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    rcases p12090_3 (m.d 0 3) (by simp) with h12093 | h12093
                                    · rcases p12090_3 (m.d 1 3) (by simp) with h12094 | h12094
                                      · rcases p12090_3 (m.d 2 3) (by simp) with h12095 | h12095
                                        · linarith only [h12095, h9886, hlam]
                                        · rcases p12090_3 (m.d 3 4) (by simp) with h12097 | h12097
                                          · linarith only [h12097, h9889, hlam]
                                          · rcases p12090_3 (m.d 3 5) (by simp) with h12099 | h12099
                                            · linarith only [h12099, h9890, hlam]
                                            · linarith only [h11730, h12099, hlam]
                                      · linarith only [h11319, h12094, hlam]
                                    · linarith only [h12093, h9886, hlam]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [h11729, h11730, h9890, hlam, p12090_2]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [h11729, h11730, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p12090_1]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [h11319, h11729, h11730, h9890, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12090_1]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [hlam, p12090_0]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    rcases p12090_3 (m.d 0 3) (by simp) with h12108 | h12108
                                    · linarith only [h12108, h7600, hlam]
                                    · linarith only [h12108, h9886, hlam]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [h11729, h11730, h7600, h9890, hlam, p12090_2]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [h11324, h11729, h11730, h8836, h9666, hc01, hc13, hc34, hc45, hlam, hphi, p11992_1, p12090_1]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [h9886, hlam, p12090_0]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [h11319, hlam, p12090_0]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [hlam, p12090_0]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [h11730, h9890, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p12090_1]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [h11730, hlam, p12090_0]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [h9889, hlam, p12090_0]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [h11322, hlam, p12090_0]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [h11729, hlam, p12090_0]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [hlam, p12090_0]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [h11990, hlam, p12090_1]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [h9890, hlam, p12090_0]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [h11323, hlam, p12090_0]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [h0, h11324, h11729, h8836, h9666, h9886, h9890, hc01, hc12, hc34, hc45, hlam, hphi, p11992_1, p12090_1]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    rcases p12090_3 (m.d 0 3) (by simp) with h12126 | h12126
                                    · rcases p12090_3 (m.d 1 3) (by simp) with h12127 | h12127
                                      · rcases p12090_3 (m.d 2 3) (by simp) with h12128 | h12128
                                        · linarith only [h11730, h12128, hlam]
                                        · linarith only [h11729, h12128, hlam]
                                      · linarith only [h11322, h12127, hlam]
                                    · linarith only [h12126, h9889, hlam]
                                  · have p12090_0 := h12090c.1
                                    have p12090_1 := h12090c.2.1
                                    have p12090_2 := h12090c.2.2.1
                                    have p12090_3 := h12090c.2.2.2
                                    linarith only [hlam, p12090_0]
                          · linarith only [h11321, h12083, hlam]
                        · linarith only [h12082, hlam, p12061_0]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [h9886, h9890, hc12, hlam, hphi, ht01, ht0b, ht5b, p12061_1, u5ehi3]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [hlam, p12061_0]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        rcases p12061_3 (m.d 0 2) (by simp) with h12138 | h12138
                        · linarith only [h0, h12138, hlam]
                        · linarith only [h12138, h9886, hlam]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        rcases p12061_3 (m.d 0 2) (by simp) with h12141 | h12141
                        · linarith only [h0, h12141, hlam]
                        · linarith only [h12141, h9887, hlam]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        rcases p12061_3 (m.d 0 2) (by simp) with h12144 | h12144
                        · linarith only [h0, h12144, hlam]
                        · linarith only [h12144, h9888, hlam]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [h9886, hlam, p12061_0]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [h11319, hlam, p12061_0]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [hlam, p12061_0]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [h11730, h9886, h9890, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p12061_1]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [h11730, hlam, p12061_0]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [h9887, hlam, p12061_0]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [h11320, hlam, p12061_0]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [h11729, hlam, p12061_1]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [hlam, p12061_0]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [h11988, hlam, p12061_1]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [h9888, hlam, p12061_0]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [h11321, hlam, p12061_0]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [h0, h11324, h11729, h8836, h9666, h9888, hc01, hc12, hc34, hc45, hlam, hphi, p11992_1, p12061_1]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        rcases p12061_3 (m.d 0 2) (by simp) with h12160 | h12160
                        · rcases p12061_3 (m.d 1 2) (by simp) with h12161 | h12161
                          · rcases p12061_3 (m.d 2 3) (by simp) with h12162 | h12162
                            · linarith only [h11730, h12162, hlam]
                            · linarith only [h11729, h12162, hlam]
                          · linarith only [h11320, h12161, hlam]
                        · linarith only [h12160, h9887, hlam]
                      · have p12061_0 := h12061c.1
                        have p12061_1 := h12061c.2.1
                        have p12061_2 := h12061c.2.2.1
                        have p12061_3 := h12061c.2.2.2
                        linarith only [hlam, p12061_0]
                    · linarith only [h12060, h9891, hlam]
                · linarith only [h12057, h9889, hlam]
              · linarith only [h12056, h9887, hlam]
          · have p11992_0 := h11992c.1
            have p11992_1 := h11992c.2.1
            have p11992_2 := h11992c.2.2.1
            have p11992_3 := h11992c.2.2.2
            linarith only [hlam, p11992_0]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h12172 | h12172
    · linarith only [h11324, h11729, h12172, h8836, h9889, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h12174 | h12174
      · linarith only [h11324, h12174, h8836, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h12176 | h12176
        · linarith only [h11324, h12176, h8836, h9889, hlam]
        · rcases h0bigk with h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [hlam, p12178_0]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [h0, hlam, p12178_1]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [h7600, hlam, p12178_0]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [h8836, hlam, p12178_1]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [h9666, hlam, p12178_1]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            rcases p12178_3 (m.d 0 1) (by simp) with h12184 | h12184
            · linarith only [h0, h12184, hlam]
            · rcases p12178_3 (m.d 0 2) (by simp) with h12186 | h12186
              · rcases p12178_3 (m.d 0 3) (by simp) with h12187 | h12187
                · linarith only [h12187, h9886, hlam]
                · linarith only [h12187, h7600, hlam]
              · linarith only [h0, h12186, hlam]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [hlam, p12178_0]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [h0, h11729, h9889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12178_1]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            rcases p12178_3 (m.d 0 1) (by simp) with h12193 | h12193
            · linarith only [h0, h12193, hlam]
            · rcases p12178_3 (m.d 0 2) (by simp) with h12195 | h12195
              · rcases p12178_3 (m.d 0 3) (by simp) with h12196 | h12196
                · linarith only [h12196, h9886, hlam]
                · linarith only [h12196, h9889, hlam]
              · linarith only [h12195, h9887, hlam]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            rcases p12178_3 (m.d 0 1) (by simp) with h12200 | h12200
            · linarith only [h0, h12200, hlam]
            · rcases p12178_3 (m.d 0 2) (by simp) with h12202 | h12202
              · rcases p12178_3 (m.d 0 3) (by simp) with h12203 | h12203
                · linarith only [h12203, h9886, hlam]
                · linarith only [h12203, h9890, hlam]
              · linarith only [h12202, h9888, hlam]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            rcases p12178_3 (m.d 0 1) (by simp) with h12207 | h12207
            · linarith only [h12207, h7600, hlam]
            · rcases p12178_3 (m.d 0 2) (by simp) with h12209 | h12209
              · rcases p12178_3 (m.d 0 3) (by simp) with h12210 | h12210
                · rcases p12178_3 (m.d 0 4) (by simp) with h12211 | h12211
                  · linarith only [h12211, h9889, hlam]
                  · linarith only [h12211, h8836, hlam]
                · linarith only [h12210, h7600, hlam]
              · linarith only [h0, h12209, hlam]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [h9886, hlam, p12178_1]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [hlam, p12178_0]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            rcases p12178_3 (m.d 0 1) (by simp) with h12218 | h12218
            · linarith only [h12218, h7600, hlam]
            · rcases p12178_3 (m.d 0 2) (by simp) with h12220 | h12220
              · rcases p12178_3 (m.d 0 3) (by simp) with h12221 | h12221
                · rcases p12178_3 (m.d 0 4) (by simp) with h12222 | h12222
                  · linarith only [h12222, h9889, hlam]
                  · rcases p12178_3 (m.d 0 5) (by simp) with h12224 | h12224
                    · linarith only [h12224, h9890, hlam]
                    · linarith only [h12224, h9891, hlam]
                · linarith only [h12221, h9889, hlam]
              · linarith only [h12220, h9887, hlam]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            rcases p12178_3 (m.d 0 1) (by simp) with h12229 | h12229
            · linarith only [h12229, h7600, hlam]
            · rcases p12178_3 (m.d 0 2) (by simp) with h12231 | h12231
              · rcases p12178_3 (m.d 0 3) (by simp) with h12232 | h12232
                · rcases p12178_3 (m.d 0 4) (by simp) with h12233 | h12233
                  · linarith only [h12233, h9889, hlam]
                  · rcases p12178_3 (m.d 0 5) (by simp) with h12235 | h12235
                    · linarith only [h12235, h9890, hlam]
                    · rcases h2bigk with h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c | h12237c
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [hlam, p12237_0]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [h0, hlam, p12237_1]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [h11729, h9886, h9889, h9891, hlam, p12178_1, p12237_2]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        rcases p12237_3 (m.d 0 2) (by simp) with h12241 | h12241
                        · rcases p12237_3 (m.d 1 2) (by simp) with h12242 | h12242
                          · rcases p12237_3 (m.d 2 3) (by simp) with h12243 | h12243
                            · linarith only [h12243, h9886, hlam]
                            · rcases p12237_3 (m.d 2 4) (by simp) with h12245 | h12245
                              · linarith only [h12245, hlam, p12237_0]
                              · rcases p12237_3 (m.d 2 5) (by simp) with h12247 | h12247
                                · linarith only [h12247, h9888, hlam]
                                · linarith only [h12174, h12247, hlam]
                          · linarith only [h11320, h12242, hlam]
                        · linarith only [h12241, hlam, p12237_0]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        rcases p12237_3 (m.d 0 2) (by simp) with h12252 | h12252
                        · rcases p12237_3 (m.d 1 2) (by simp) with h12253 | h12253
                          · rcases p12237_3 (m.d 2 3) (by simp) with h12254 | h12254
                            · linarith only [h12254, h9886, hlam]
                            · rcases p12237_3 (m.d 2 4) (by simp) with h12256 | h12256
                              · linarith only [h12256, h9887, hlam]
                              · rcases p12237_3 (m.d 2 5) (by simp) with h12258 | h12258
                                · linarith only [h12258, hlam, p12237_0]
                                · rcases h3bigk with h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c | h12260c
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [hlam, p12260_0]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [h7600, hlam, p12260_1]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [h11729, h9889, h9891, hlam, p12178_1, p12260_2]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    rcases p12260_3 (m.d 0 3) (by simp) with h12264 | h12264
                                    · rcases p12260_3 (m.d 1 3) (by simp) with h12265 | h12265
                                      · rcases p12260_3 (m.d 2 3) (by simp) with h12266 | h12266
                                        · linarith only [h12266, h9886, hlam]
                                        · rcases p12260_3 (m.d 3 4) (by simp) with h12268 | h12268
                                          · linarith only [h12268, hlam, p12260_0]
                                          · rcases p12260_3 (m.d 3 5) (by simp) with h12270 | h12270
                                            · linarith only [h12270, h9890, hlam]
                                            · linarith only [h12176, h12270, hlam]
                                      · linarith only [h11322, h12265, hlam]
                                    · linarith only [h12264, hlam, p12260_0]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    rcases p12260_3 (m.d 0 3) (by simp) with h12275 | h12275
                                    · rcases p12260_3 (m.d 1 3) (by simp) with h12276 | h12276
                                      · rcases p12260_3 (m.d 2 3) (by simp) with h12277 | h12277
                                        · linarith only [h12277, h9886, hlam]
                                        · rcases p12260_3 (m.d 3 4) (by simp) with h12279 | h12279
                                          · linarith only [h12279, h9889, hlam]
                                          · rcases p12260_3 (m.d 3 5) (by simp) with h12281 | h12281
                                            · linarith only [h12281, hlam, p12260_0]
                                            · rcases h5bigk with h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c | h12283c
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [hlam, p12283_0]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h9666, hlam, p12283_1]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h12174, h9886, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p12178_1, p12283_1]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h0, h11729, h12176, h9886, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12178_1, p12283_1]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h9891, hlam, p12283_1]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h11324, h11729, h12176, h9890, hc23, hc45, hlam, hphi, ht34, p12283_1]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [hlam, p12283_0]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                rcases p12283_3 (m.d 0 5) (by simp) with h12291 | h12291
                                                · linarith only [h12291, h9666, hlam]
                                                · linarith only [h12291, h9888, hlam]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h11324, h11729, h12176, hc23, hc45, hlam, hphi, ht34, p12283_1]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h11324, hlam, p12283_1]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h9888, hlam, p12283_1]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h11321, hlam, p12283_1]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [hlam, p12283_0]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h12172, hlam, p12283_1]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h12174, hlam, p12283_1]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h9890, hlam, p12283_0]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h11323, hlam, p12283_0]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h0, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, p12260_1, p12283_1, u5ehi2]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [hlam, p12283_0]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h12176, hlam, p12283_1]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h11729, h9889, h9891, hc23, hc45, hlam, hphi, ht34, p12283_1]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h9666, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12283_1]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                rcases p12283_3 (m.d 0 5) (by simp) with h12308 | h12308
                                                · linarith only [h12308, h9891, hlam]
                                                · linarith only [h12308, h9888, hlam]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [h11729, h12176, hc23, hc45, hlam, hphi, ht34, p12283_1]
                                              · have p12283_0 := h12283c.1
                                                have p12283_1 := h12283c.2.1
                                                have p12283_2 := h12283c.2.2.1
                                                have p12283_3 := h12283c.2.2.2
                                                linarith only [hlam, p12283_0]
                                      · linarith only [h11323, h12276, hlam]
                                    · linarith only [h12275, hlam, p12260_0]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [h11319, h11729, h9889, h9891, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12178_1, p12260_1]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [hlam, p12260_0]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [h11729, h7600, h9889, h9891, hlam, p12178_1, p12260_2]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    rcases p12260_3 (m.d 0 3) (by simp) with h12318 | h12318
                                    · linarith only [h12318, h7600, hlam]
                                    · linarith only [h12318, h9889, hlam]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    rcases p12260_3 (m.d 0 3) (by simp) with h12321 | h12321
                                    · linarith only [h12321, h7600, hlam]
                                    · linarith only [h12321, h9890, hlam]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [h9886, hlam, p12260_0]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [h11319, hlam, p12260_0]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [hlam, p12260_0]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [h11729, hlam, p12260_0]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [h12172, hlam, p12260_0]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [h9889, hlam, p12260_0]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [h11322, hlam, p12260_0]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [h9886, h9889, h9891, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12178_1, p12260_1]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [hlam, p12260_0]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [h12176, hlam, p12260_1]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [h9890, hlam, p12260_0]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [h11323, hlam, p12260_0]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [h0, h9886, h9890, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12178_1, p12260_1]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [h0, h9886, h9890, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12178_1, p12260_1]
                                  · have p12260_0 := h12260c.1
                                    have p12260_1 := h12260c.2.1
                                    have p12260_2 := h12260c.2.2.1
                                    have p12260_3 := h12260c.2.2.2
                                    linarith only [hlam, p12260_0]
                          · linarith only [h11321, h12253, hlam]
                        · linarith only [h12252, hlam, p12237_0]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [h9886, h9891, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p12178_1, p12237_1]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [hlam, p12237_0]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [h0, h11729, h9886, h9889, h9891, hlam, p12178_1, p12237_2]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        rcases p12237_3 (m.d 0 2) (by simp) with h12344 | h12344
                        · linarith only [h0, h12344, hlam]
                        · linarith only [h12344, h9887, hlam]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        rcases p12237_3 (m.d 0 2) (by simp) with h12347 | h12347
                        · linarith only [h0, h12347, hlam]
                        · linarith only [h12347, h9888, hlam]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [h9886, hlam, p12237_0]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [h11319, hlam, p12237_0]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [hlam, p12237_0]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [h11729, hlam, p12237_0]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [h12172, hlam, p12237_0]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [h9887, hlam, p12237_0]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [h11320, hlam, p12237_0]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [h9886, h9887, h9891, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12178_1, p12237_1]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [hlam, p12237_0]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [h12174, hlam, p12237_1]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [h9888, hlam, p12237_0]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [h11321, hlam, p12237_0]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [h0, h9886, h9888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12178_1, p12237_1]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [h0, h9886, h9888, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p12178_1, p12237_1]
                      · have p12237_0 := h12237c.1
                        have p12237_1 := h12237c.2.1
                        have p12237_2 := h12237c.2.2.1
                        have p12237_3 := h12237c.2.2.2
                        linarith only [hlam, p12237_0]
                · linarith only [h12232, h9890, hlam]
              · linarith only [h12231, h9888, hlam]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [h9891, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12178_1]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [h9887, hlam, p12178_0]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [h9889, hlam, p12178_0]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [hlam, p12178_0]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [h9891, hlam, p12178_0]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            rcases p12178_3 (m.d 0 1) (by simp) with h12372 | h12372
            · linarith only [h12372, h9666, hlam]
            · rcases p12178_3 (m.d 0 2) (by simp) with h12374 | h12374
              · rcases p12178_3 (m.d 0 3) (by simp) with h12375 | h12375
                · rcases p12178_3 (m.d 0 4) (by simp) with h12376 | h12376
                  · linarith only [h12376, h9891, hlam]
                  · linarith only [h12376, h8836, hlam]
                · linarith only [h12375, h7600, hlam]
              · linarith only [h0, h12374, hlam]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [h9888, hlam, p12178_1]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [h9890, hlam, p12178_0]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [h11729, h9889, h9891, hc23, hc45, hlam, hphi, ht34, p12178_1]
          · have p12178_0 := h12178c.1
            have p12178_1 := h12178c.2.1
            have p12178_2 := h12178c.2.2.1
            have p12178_3 := h12178c.2.2.2
            linarith only [hlam, p12178_0]

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9890 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9891 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11319 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11320 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11321 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11322 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11323 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  rcases m.htr 1 4 5 (by decide) (by decide) with h11324 | h11324
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h11319 h11320 h11321 h11322 h11323 h11324
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h11319 h11320 h11321 h11322 h11323 h11324

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9890 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9891 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11319 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11320 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11321 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11322 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11323 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  linarith only [h0, h11323, h7600, h9886, h9890, hc01, hc12, hlam, hphi]

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9890 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9891 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11319 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11320 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11321 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11322 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  rcases m.htr 1 3 5 (by decide) (by decide) with h11323 | h11323
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h11319 h11320 h11321 h11322 h11323
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h11319 h11320 h11321 h11322 h11323

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9890 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9891 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11319 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11320 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11321 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11322 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  linarith only [h11322, h7600, h9889, hlam]

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9890 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9891 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11319 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11320 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11321 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  rcases m.htr 1 3 4 (by decide) (by decide) with h11322 | h11322
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h11319 h11320 h11321 h11322
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h11319 h11320 h11321 h11322

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9890 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9891 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11319 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11320 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11321 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  linarith only [h0, h11321, h9888, hlam]

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9890 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9891 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11319 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11320 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  rcases m.htr 1 2 5 (by decide) (by decide) with h11321 | h11321
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h11319 h11320 h11321
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h11319 h11320 h11321

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9890 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9891 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11319 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11320 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  linarith only [h0, h11320, h9887, hlam]

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9890 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9891 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11319 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  rcases m.htr 1 2 4 (by decide) (by decide) with h11320 | h11320
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h11319 h11320
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h11319 h11320

end R2N4
