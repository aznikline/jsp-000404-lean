import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1_x1_x0_x0_x1 (m : N7Model)
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
    (h9967 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9968 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9970 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h9972 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h9974 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9975 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h9976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  rcases m.htr 2 3 4 (by decide) (by decide) with h10764 | h10764
  · rcases m.htr 2 3 5 (by decide) (by decide) with h10765 | h10765
    · rcases m.htr 2 4 5 (by decide) (by decide) with h10766 | h10766
      · rcases m.htr 3 4 5 (by decide) (by decide) with h10767 | h10767
        · linarith only [h10767, h9974, h9976, hlam]
        · rcases h0bigk with h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c | h10769c
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [hlam, p10769_0]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            rcases p10769_3 (m.d 0 1) (by simp) with h10771 | h10771
            · rcases p10769_3 (m.d 0 2) (by simp) with h10772 | h10772
              · linarith only [h0, h10772, hlam]
              · rcases p10769_3 (m.d 0 3) (by simp) with h10774 | h10774
                · linarith only [h1, h10774, hlam]
                · linarith only [h10774, h4, hlam]
            · linarith only [h0, h10771, hlam]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [h9965, h9967, h9970, h9976, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10769_1]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [h9967, h9970, h9976, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10769_1]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            rcases p10769_3 (m.d 0 1) (by simp) with h10780 | h10780
            · rcases p10769_3 (m.d 0 2) (by simp) with h10781 | h10781
              · linarith only [h0, h10781, hlam]
              · rcases p10769_3 (m.d 0 3) (by simp) with h10783 | h10783
                · linarith only [h1, h10783, hlam]
                · linarith only [h10783, h9966, hlam]
            · linarith only [h10780, h3, hlam]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [h0, hlam, p10769_0]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [hlam, p10769_0]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [h4, hlam, p10769_0]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [h7821, hlam, p10769_1]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [h9029, hlam, p10769_0]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [h1, hlam, p10769_1]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            rcases p10769_3 (m.d 0 1) (by simp) with h10793 | h10793
            · rcases p10769_3 (m.d 0 2) (by simp) with h10794 | h10794
              · linarith only [h10794, h4, hlam]
              · rcases p10769_3 (m.d 0 3) (by simp) with h10796 | h10796
                · rcases p10769_3 (m.d 0 4) (by simp) with h10797 | h10797
                  · linarith only [h10797, h9965, hlam]
                  · linarith only [h10797, h7821, hlam]
                · linarith only [h10796, h4, hlam]
            · linarith only [h0, h10793, hlam]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [hlam, p10769_0]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [h9967, h9970, h9976, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10769_1]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [h4, h9967, h9970, h9976, hc12, hc23, hlam, hphi, p10769_1]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [h2, hlam, p10769_0]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            rcases p10769_3 (m.d 0 1) (by simp) with h10806 | h10806
            · rcases p10769_3 (m.d 0 2) (by simp) with h10807 | h10807
              · linarith only [h10807, h7821, hlam]
              · rcases p10769_3 (m.d 0 3) (by simp) with h10809 | h10809
                · rcases p10769_3 (m.d 0 4) (by simp) with h10810 | h10810
                  · rcases p10769_3 (m.d 0 5) (by simp) with h10811 | h10811
                    · linarith only [h10811, h9967, hlam]
                    · linarith only [h10811, h9029, hlam]
                  · linarith only [h10810, h7821, hlam]
                · linarith only [h10809, h4, hlam]
            · linarith only [h0, h10806, hlam]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [h9965, hlam, p10769_0]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [hlam, p10769_0]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [h10764, h7821, h9967, h9970, h9976, hc12, hc23, hlam, hphi, p10769_1]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [h3, hlam, p10769_0]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            rcases p10769_3 (m.d 0 1) (by simp) with h10821 | h10821
            · rcases p10769_3 (m.d 0 2) (by simp) with h10822 | h10822
              · linarith only [h10822, h9029, hlam]
              · rcases p10769_3 (m.d 0 3) (by simp) with h10824 | h10824
                · rcases p10769_3 (m.d 0 4) (by simp) with h10825 | h10825
                  · rcases p10769_3 (m.d 0 5) (by simp) with h10826 | h10826
                    · rcases h2bigk with h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [hlam, p10827_0]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10769_1, p10827_1]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [h4, hlam, p10827_0]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [h7821, hlam, p10827_0]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [h9029, hlam, p10827_0]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [h0, hlam, p10827_0]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [hlam, p10827_0]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [h9968, hlam, p10827_0]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [h9970, hlam, p10827_0]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [h9972, hlam, p10827_0]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        rcases p10827_3 (m.d 0 2) (by simp) with h10838 | h10838
                        · linarith only [h10838, hlam, p10827_0]
                        · rcases p10827_3 (m.d 1 2) (by simp) with h10840 | h10840
                          · linarith only [h10840, h9968, hlam]
                          · rcases p10827_3 (m.d 2 3) (by simp) with h10842 | h10842
                            · rcases p10827_3 (m.d 2 4) (by simp) with h10843 | h10843
                              · linarith only [h10764, h10843, hlam]
                              · linarith only [h10843, h7821, hlam]
                            · linarith only [h10842, hlam, p10827_0]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        rcases p10827_3 (m.d 0 2) (by simp) with h10847 | h10847
                        · linarith only [h10847, h4, hlam]
                        · linarith only [h0, h10847, hlam]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [hlam, p10827_0]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [h10766, h9029, hc02, hc23, hlam, hphi, p10769_1, p10827_1]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [h0, h9029, hc12, hc23, hlam, hphi, p10769_1, p10827_1]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        rcases p10827_3 (m.d 0 2) (by simp) with h10853 | h10853
                        · linarith only [h10853, hlam, p10827_0]
                        · rcases p10827_3 (m.d 1 2) (by simp) with h10855 | h10855
                          · linarith only [h10855, h9970, hlam]
                          · rcases p10827_3 (m.d 2 3) (by simp) with h10857 | h10857
                            · rcases p10827_3 (m.d 2 4) (by simp) with h10858 | h10858
                              · rcases p10827_3 (m.d 2 5) (by simp) with h10859 | h10859
                                · linarith only [h10766, h10859, hlam]
                                · linarith only [h10859, h9029, hlam]
                              · linarith only [h10858, hlam, p10827_0]
                            · linarith only [h10857, h4, hlam]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        rcases p10827_3 (m.d 0 2) (by simp) with h10864 | h10864
                        · linarith only [h10864, h7821, hlam]
                        · linarith only [h0, h10864, hlam]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [h10764, hlam, p10827_1]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [hlam, p10827_0]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [h0, h9029, hc12, hc24, hlam, hphi, p10769_1, p10827_1]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        rcases p10827_3 (m.d 0 2) (by simp) with h10870 | h10870
                        · linarith only [h10870, hlam, p10827_0]
                        · rcases p10827_3 (m.d 1 2) (by simp) with h10872 | h10872
                          · linarith only [h10872, h9972, hlam]
                          · rcases p10827_3 (m.d 2 3) (by simp) with h10874 | h10874
                            · rcases p10827_3 (m.d 2 4) (by simp) with h10875 | h10875
                              · rcases p10827_3 (m.d 2 5) (by simp) with h10876 | h10876
                                · rcases h3bigk with h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c | h10877c
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    linarith only [hlam, p10877_0]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    rcases p10877_3 (m.d 0 3) (by simp) with h10879 | h10879
                                    · rcases p10877_3 (m.d 1 3) (by simp) with h10880 | h10880
                                      · linarith only [h1, h10880, hlam]
                                      · rcases p10877_3 (m.d 2 3) (by simp) with h10882 | h10882
                                        · rcases p10877_3 (m.d 3 4) (by simp) with h10883 | h10883
                                          · linarith only [h10883, h9965, hlam]
                                          · rcases p10877_3 (m.d 3 5) (by simp) with h10885 | h10885
                                            · linarith only [h10885, h9966, hlam]
                                            · rcases h5bigk with h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c | h10887c
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [hlam, p10887_0]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h9029, h9972, hc12, hc25, hlam, hphi, p10887_1]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h9029, hlam, p10887_0]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                rcases p10887_3 (m.d 0 5) (by simp) with h10891 | h10891
                                                · rcases p10887_3 (m.d 1 5) (by simp) with h10892 | h10892
                                                  · linarith only [h10892, h3, hlam]
                                                  · linarith only [h10892, h9975, hlam]
                                                · linarith only [h10891, h9966, hlam]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h4, h9965, h9967, h9970, h9976, hc12, hc23, hlam, hphi, p10887_1]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h3, hlam, p10887_0]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [hlam, p10887_0]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h9972, hlam, p10887_0]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h10767, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10887_1]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h9976, hlam, p10887_1]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h0, h10764, h10766, hc12, hc23, hlam, hphi, p10769_1, p10887_1]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h10764, h10766, h9972, hc12, hc23, hlam, hphi, p10887_1]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [hlam, p10887_0]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                rcases p10887_3 (m.d 0 5) (by simp) with h10905 | h10905
                                                · linarith only [h10905, h9029, hlam]
                                                · linarith only [h10905, h9966, hlam]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h10764, h10766, h9970, h9976, hc12, hc23, hlam, hphi, p10887_1]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h9966, hlam, p10887_0]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h9975, hlam, p10887_0]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h10765, hlam, p10887_0]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [hlam, p10887_0]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h10767, hlam, p10887_1]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h9967, hlam, p10887_0]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h9970, h9976, hc12, hc45, hlam, hphi, ht23, ht34, p10887_1]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h10766, hlam, p10887_0]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [h10764, h10767, h7821, h9967, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10887_1]
                                              · have p10887_0 := h10887c.1
                                                have p10887_1 := h10887c.2.1
                                                have p10887_2 := h10887c.2.2.1
                                                have p10887_3 := h10887c.2.2.2
                                                linarith only [hlam, p10887_0]
                                        · linarith only [h10882, h9968, hlam]
                                    · linarith only [h1, h10879, hlam]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    linarith only [h4, hlam, p10877_1]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    rcases p10877_3 (m.d 0 3) (by simp) with h10922 | h10922
                                    · rcases p10877_3 (m.d 1 3) (by simp) with h10923 | h10923
                                      · linarith only [h1, h10923, hlam]
                                      · linarith only [h10923, h9974, hlam]
                                    · linarith only [h10922, hlam, p10877_0]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    rcases p10877_3 (m.d 0 3) (by simp) with h10927 | h10927
                                    · rcases p10877_3 (m.d 1 3) (by simp) with h10928 | h10928
                                      · linarith only [h1, h10928, hlam]
                                      · linarith only [h10928, h9975, hlam]
                                    · linarith only [h10927, hlam, p10877_0]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    linarith only [h1, hlam, p10877_0]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    linarith only [hlam, p10877_0]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    linarith only [h9968, hlam, p10877_1]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    rcases p10877_3 (m.d 0 3) (by simp) with h10935 | h10935
                                    · rcases p10877_3 (m.d 1 3) (by simp) with h10936 | h10936
                                      · rcases p10877_3 (m.d 2 3) (by simp) with h10937 | h10937
                                        · rcases p10877_3 (m.d 3 4) (by simp) with h10938 | h10938
                                          · linarith only [h10938, hlam, p10877_0]
                                          · rcases p10877_3 (m.d 3 5) (by simp) with h10940 | h10940
                                            · linarith only [h10940, h9975, hlam]
                                            · linarith only [h10767, h10940, hlam]
                                        · linarith only [h10764, h10937, hlam]
                                      · linarith only [h10936, hlam, p10877_0]
                                    · linarith only [h10935, h9965, hlam]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    rcases p10877_3 (m.d 0 3) (by simp) with h10946 | h10946
                                    · rcases p10877_3 (m.d 1 3) (by simp) with h10947 | h10947
                                      · rcases p10877_3 (m.d 2 3) (by simp) with h10948 | h10948
                                        · rcases p10877_3 (m.d 3 4) (by simp) with h10949 | h10949
                                          · linarith only [h10949, h9974, hlam]
                                          · rcases p10877_3 (m.d 3 5) (by simp) with h10951 | h10951
                                            · linarith only [h10951, hlam, p10877_0]
                                            · rcases h5bigk with h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [hlam, p10953_0]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h10764, h10766, h9029, h9970, h9976, hc12, hc23, hlam, hphi, p10953_1]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h9029, hlam, p10953_0]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                rcases p10953_3 (m.d 0 5) (by simp) with h10957 | h10957
                                                · rcases p10953_3 (m.d 1 5) (by simp) with h10958 | h10958
                                                  · linarith only [h10958, h3, hlam]
                                                  · linarith only [h10958, h9975, hlam]
                                                · linarith only [h10957, h9966, hlam]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h10764, h10766, h9029, h9970, h9976, hc12, hc23, hlam, hphi, p10953_1]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h3, hlam, p10953_0]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [hlam, p10953_0]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h9972, hlam, p10953_0]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h10767, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10953_1]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h9976, hlam, p10953_1]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h0, h10764, h10766, hc12, hc23, hlam, hphi, p10769_1, p10953_1]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h10764, h10766, h9972, hc12, hc23, hlam, hphi, p10953_1]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [hlam, p10953_0]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                rcases p10953_3 (m.d 0 5) (by simp) with h10971 | h10971
                                                · linarith only [h10971, h9029, hlam]
                                                · linarith only [h10971, h9966, hlam]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h10764, h10766, h9970, h9976, hc12, hc23, hlam, hphi, p10953_1]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h9966, hlam, p10953_0]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h9975, hlam, p10953_0]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h10765, hlam, p10953_0]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [hlam, p10953_0]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h10767, hlam, p10953_1]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h9967, hlam, p10953_0]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h9970, h9976, hc12, hc45, hlam, hphi, ht23, ht34, p10953_1]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h10766, hlam, p10953_0]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [h10767, h9965, h9967, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p10953_1]
                                              · have p10953_0 := h10953c.1
                                                have p10953_1 := h10953c.2.1
                                                have p10953_2 := h10953c.2.2.1
                                                have p10953_3 := h10953c.2.2.2
                                                linarith only [hlam, p10953_0]
                                        · linarith only [h10765, h10948, hlam]
                                      · linarith only [h10947, hlam, p10877_0]
                                    · linarith only [h10946, h9966, hlam]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    linarith only [h0, h9966, hc12, hc23, hlam, hphi, p10769_1, p10877_1]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    rcases p10877_3 (m.d 0 3) (by simp) with h10989 | h10989
                                    · linarith only [h10989, h4, hlam]
                                    · linarith only [h1, h10989, hlam]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    linarith only [hlam, p10877_0]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    rcases p10877_3 (m.d 0 3) (by simp) with h10993 | h10993
                                    · linarith only [h10993, h4, hlam]
                                    · linarith only [h10993, h9965, hlam]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    rcases p10877_3 (m.d 0 3) (by simp) with h10996 | h10996
                                    · linarith only [h10996, h4, hlam]
                                    · linarith only [h10996, h9966, hlam]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    linarith only [h9965, hlam, p10877_0]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    linarith only [h9974, hlam, p10877_0]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    linarith only [h10764, hlam, p10877_0]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    linarith only [hlam, p10877_0]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    linarith only [h10767, hlam, p10877_1]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    linarith only [h9966, hlam, p10877_0]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    linarith only [h9975, hlam, p10877_0]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    linarith only [h10765, hlam, p10877_0]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    linarith only [h1, h9975, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10877_1]
                                  · have p10877_0 := h10877c.1
                                    have p10877_1 := h10877c.2.1
                                    have p10877_2 := h10877c.2.2.1
                                    have p10877_3 := h10877c.2.2.2
                                    linarith only [hlam, p10877_0]
                                · linarith only [h10876, hlam, p10827_0]
                              · linarith only [h10875, h7821, hlam]
                            · linarith only [h10874, h4, hlam]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        rcases p10827_3 (m.d 0 2) (by simp) with h11012 | h11012
                        · linarith only [h11012, h9029, hlam]
                        · linarith only [h0, h11012, hlam]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [h10765, hlam, p10827_1]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [h10766, hlam, p10827_0]
                      · have p10827_0 := h10827c.1
                        have p10827_1 := h10827c.2.1
                        have p10827_2 := h10827c.2.2.1
                        have p10827_3 := h10827c.2.2.2
                        linarith only [hlam, p10827_0]
                    · linarith only [h10826, h9029, hlam]
                  · linarith only [h10825, h7821, hlam]
                · linarith only [h10824, h4, hlam]
            · linarith only [h0, h10821, hlam]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [h9966, hlam, p10769_0]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [h9967, hlam, p10769_1]
          · have p10769_0 := h10769c.1
            have p10769_1 := h10769c.2.1
            have p10769_2 := h10769c.2.2.1
            have p10769_3 := h10769c.2.2.2
            linarith only [hlam, p10769_0]
      · linarith only [h10766, h7821, h9967, hlam]
    · linarith only [h10765, h4, h9965, h9967, h9975, h9976, hlam]
  · linarith only [h10764, h4, h9965, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1_x1_x0_x0 (m : N7Model)
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
    (h9967 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9968 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9970 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h9972 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h9974 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9975 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  rcases m.htr 1 4 5 (by decide) (by decide) with h9976 | h9976
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h9968 h9970 h9972 h9974 h9975 h9976
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h9968 h9970 h9972 h9974 h9975 h9976

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1_x1_x0_x1 (m : N7Model)
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
    (h9967 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9968 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9970 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h9972 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h9974 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9975 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  rcases m.htr 1 4 5 (by decide) (by decide) with h11028 | h11028
  · linarith only [h11028, h9974, h9975, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h11030 | h11030
    · rcases m.htr 2 3 5 (by decide) (by decide) with h11031 | h11031
      · rcases m.htr 2 4 5 (by decide) (by decide) with h11032 | h11032
        · rcases m.htr 3 4 5 (by decide) (by decide) with h11033 | h11033
          · linarith only [h11028, h11033, h4, h9966, h9974, h9975, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · rcases h0bigk with h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c | h11035c
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [hlam, p11035_0]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              rcases p11035_3 (m.d 0 1) (by simp) with h11037 | h11037
              · rcases p11035_3 (m.d 0 2) (by simp) with h11038 | h11038
                · linarith only [h0, h11038, hlam]
                · rcases p11035_3 (m.d 0 3) (by simp) with h11040 | h11040
                  · linarith only [h1, h11040, hlam]
                  · linarith only [h11040, h4, hlam]
              · linarith only [h0, h11037, hlam]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [h11033, h9965, h9967, h9975, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p11035_1]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [h11033, h9967, h9974, h9975, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11035_1]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [h9966, h9974, h9975, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11035_1]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [h0, hlam, p11035_0]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [hlam, p11035_0]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [h4, hlam, p11035_0]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [h7821, hlam, p11035_1]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [h9029, hlam, p11035_0]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [h1, hlam, p11035_1]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              rcases p11035_3 (m.d 0 1) (by simp) with h11053 | h11053
              · rcases p11035_3 (m.d 0 2) (by simp) with h11054 | h11054
                · linarith only [h11054, h4, hlam]
                · rcases p11035_3 (m.d 0 3) (by simp) with h11056 | h11056
                  · rcases p11035_3 (m.d 0 4) (by simp) with h11057 | h11057
                    · linarith only [h11057, h9965, hlam]
                    · linarith only [h11057, h7821, hlam]
                  · linarith only [h11056, h4, hlam]
              · linarith only [h0, h11053, hlam]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [hlam, p11035_0]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [h11033, h9967, h9974, h9975, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p11035_1]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [h11033, h4, h9967, h9974, h9975, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11035_1]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [h2, hlam, p11035_0]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              rcases p11035_3 (m.d 0 1) (by simp) with h11066 | h11066
              · rcases p11035_3 (m.d 0 2) (by simp) with h11067 | h11067
                · linarith only [h11067, h7821, hlam]
                · rcases p11035_3 (m.d 0 3) (by simp) with h11069 | h11069
                  · rcases p11035_3 (m.d 0 4) (by simp) with h11070 | h11070
                    · rcases p11035_3 (m.d 0 5) (by simp) with h11071 | h11071
                      · linarith only [h11071, h9967, hlam]
                      · linarith only [h11071, h9029, hlam]
                    · linarith only [h11070, h7821, hlam]
                  · linarith only [h11069, h4, hlam]
              · linarith only [h0, h11066, hlam]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [h9965, hlam, p11035_0]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [hlam, p11035_0]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [h11033, h9967, h9974, h9975, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p11035_1]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [h3, hlam, p11035_0]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              rcases p11035_3 (m.d 0 1) (by simp) with h11081 | h11081
              · rcases p11035_3 (m.d 0 2) (by simp) with h11082 | h11082
                · linarith only [h11082, h9029, hlam]
                · rcases p11035_3 (m.d 0 3) (by simp) with h11084 | h11084
                  · rcases p11035_3 (m.d 0 4) (by simp) with h11085 | h11085
                    · rcases p11035_3 (m.d 0 5) (by simp) with h11086 | h11086
                      · rcases h2bigk with h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [hlam, p11087_0]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11035_1, p11087_1]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [h4, hlam, p11087_0]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [h7821, hlam, p11087_0]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [h9029, hlam, p11087_0]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [h0, hlam, p11087_0]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [hlam, p11087_0]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [h9968, hlam, p11087_0]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [h9970, hlam, p11087_0]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [h9972, hlam, p11087_0]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          rcases p11087_3 (m.d 0 2) (by simp) with h11098 | h11098
                          · linarith only [h11098, hlam, p11087_0]
                          · rcases p11087_3 (m.d 1 2) (by simp) with h11100 | h11100
                            · linarith only [h11100, h9968, hlam]
                            · rcases p11087_3 (m.d 2 3) (by simp) with h11102 | h11102
                              · rcases p11087_3 (m.d 2 4) (by simp) with h11103 | h11103
                                · linarith only [h11030, h11103, hlam]
                                · linarith only [h11103, h7821, hlam]
                              · linarith only [h11102, hlam, p11087_0]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          rcases p11087_3 (m.d 0 2) (by simp) with h11107 | h11107
                          · linarith only [h11107, h4, hlam]
                          · linarith only [h0, h11107, hlam]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [hlam, p11087_0]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [h11033, h7821, h9967, h9974, h9975, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11087_1]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [h9029, hc02, hc23, hlam, hphi, p11035_1, p11087_1]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          rcases p11087_3 (m.d 0 2) (by simp) with h11113 | h11113
                          · linarith only [h11113, hlam, p11087_0]
                          · rcases p11087_3 (m.d 1 2) (by simp) with h11115 | h11115
                            · linarith only [h11115, h9970, hlam]
                            · rcases p11087_3 (m.d 2 3) (by simp) with h11117 | h11117
                              · rcases p11087_3 (m.d 2 4) (by simp) with h11118 | h11118
                                · rcases p11087_3 (m.d 2 5) (by simp) with h11119 | h11119
                                  · linarith only [h11032, h11119, hlam]
                                  · linarith only [h11119, h9029, hlam]
                                · linarith only [h11118, hlam, p11087_0]
                              · linarith only [h11117, h4, hlam]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          rcases p11087_3 (m.d 0 2) (by simp) with h11124 | h11124
                          · linarith only [h11124, h7821, hlam]
                          · linarith only [h0, h11124, hlam]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [h11030, hlam, p11087_1]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [hlam, p11087_0]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [h0, h9029, hc12, hc24, hlam, hphi, p11035_1, p11087_1]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          rcases p11087_3 (m.d 0 2) (by simp) with h11130 | h11130
                          · linarith only [h11130, hlam, p11087_0]
                          · rcases p11087_3 (m.d 1 2) (by simp) with h11132 | h11132
                            · linarith only [h11132, h9972, hlam]
                            · rcases p11087_3 (m.d 2 3) (by simp) with h11134 | h11134
                              · rcases p11087_3 (m.d 2 4) (by simp) with h11135 | h11135
                                · rcases p11087_3 (m.d 2 5) (by simp) with h11136 | h11136
                                  · rcases h3bigk with h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c | h11137c
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [hlam, p11137_0]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      rcases p11137_3 (m.d 0 3) (by simp) with h11139 | h11139
                                      · rcases p11137_3 (m.d 1 3) (by simp) with h11140 | h11140
                                        · linarith only [h1, h11140, hlam]
                                        · rcases p11137_3 (m.d 2 3) (by simp) with h11142 | h11142
                                          · rcases p11137_3 (m.d 3 4) (by simp) with h11143 | h11143
                                            · linarith only [h11143, h9965, hlam]
                                            · rcases p11137_3 (m.d 3 5) (by simp) with h11145 | h11145
                                              · linarith only [h11145, h9966, hlam]
                                              · linarith only [h11145, h9975, hlam]
                                          · linarith only [h11142, h9968, hlam]
                                      · linarith only [h1, h11139, hlam]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [h4, hlam, p11137_1]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [h11033, h9965, h9967, h9974, h9975, hlam, p11137_2]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [h9974, h9975, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p11137_1]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [h1, hlam, p11137_0]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [hlam, p11137_0]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [h9968, hlam, p11137_1]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [h11033, h9967, h9975, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p11137_1]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [h9975, hlam, p11137_0]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [h0, h9966, hc12, hc23, hlam, hphi, p11035_1, p11137_1]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      rcases p11137_3 (m.d 0 3) (by simp) with h11159 | h11159
                                      · linarith only [h11159, h4, hlam]
                                      · linarith only [h1, h11159, hlam]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [hlam, p11137_0]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [h11033, h4, h9965, h9967, h9974, h9975, hlam, p11137_2]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [h9974, h9975, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11137_1]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [h9965, hlam, p11137_0]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [h9974, hlam, p11137_0]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [h11030, hlam, p11137_0]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [hlam, p11137_0]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [h11033, hlam, p11137_1]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [h9966, hlam, p11137_0]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [h11033, h9965, h9967, h9974, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p11137_1]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [h11031, hlam, p11137_0]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      rcases p11137_3 (m.d 0 3) (by simp) with h11173 | h11173
                                      · rcases p11137_3 (m.d 1 3) (by simp) with h11174 | h11174
                                        · linarith only [h11174, h9975, hlam]
                                        · linarith only [h11174, h9974, hlam]
                                      · linarith only [h11173, h9965, hlam]
                                    · have p11137_0 := h11137c.1
                                      have p11137_1 := h11137c.2.1
                                      have p11137_2 := h11137c.2.2.1
                                      have p11137_3 := h11137c.2.2.2
                                      linarith only [hlam, p11137_0]
                                  · linarith only [h11136, hlam, p11087_0]
                                · linarith only [h11135, h7821, hlam]
                              · linarith only [h11134, h4, hlam]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          rcases p11087_3 (m.d 0 2) (by simp) with h11182 | h11182
                          · linarith only [h11182, h9029, hlam]
                          · linarith only [h0, h11182, hlam]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [h11031, hlam, p11087_1]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [h11032, hlam, p11087_0]
                        · have p11087_0 := h11087c.1
                          have p11087_1 := h11087c.2.1
                          have p11087_2 := h11087c.2.2.1
                          have p11087_3 := h11087c.2.2.2
                          linarith only [hlam, p11087_0]
                      · linarith only [h11086, h9029, hlam]
                    · linarith only [h11085, h7821, hlam]
                  · linarith only [h11084, h4, hlam]
              · linarith only [h0, h11081, hlam]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [h9966, hlam, p11035_0]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [h9967, hlam, p11035_1]
            · have p11035_0 := h11035c.1
              have p11035_1 := h11035c.2.1
              have p11035_2 := h11035c.2.2.1
              have p11035_3 := h11035c.2.2.2
              linarith only [hlam, p11035_0]
        · linarith only [h0, h11032, h4, h7821, h9965, h9967, hc12, hc23, hlam, hphi]
      · linarith only [h11031, h4, h9966, hlam]
    · linarith only [h11030, h4, h9966, h9974, h9975, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1_x1_x0 (m : N7Model)
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
    (h9967 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9968 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9970 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h9972 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h9974 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  rcases m.htr 1 3 5 (by decide) (by decide) with h9975 | h9975
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h9968 h9970 h9972 h9974 h9975
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h9968 h9970 h9972 h9974 h9975

end R2N4
