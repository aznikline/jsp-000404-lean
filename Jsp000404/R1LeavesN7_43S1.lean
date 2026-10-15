import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_43S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6344000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h714 | h714
  · rcases m.htr 0 3 4 (by decide) (by decide) with h715 | h715
    · linarith only [h3, h4, h715, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h717 | h717
      · rcases m.htr 0 4 5 (by decide) (by decide) with h718 | h718
        · rcases m.htr 1 2 3 (by decide) (by decide) with h719 | h719
          · rcases m.htr 1 2 4 (by decide) (by decide) with h720 | h720
            · linarith only [h1, h4, h720, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h722 | h722
              · rcases m.htr 1 3 4 (by decide) (by decide) with h723 | h723
                · linarith only [h0, h3, h4, h715, h723, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h725 | h725
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h726 | h726
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h727 | h727
                      · linarith only [h0, h3, h4, h715, h727, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · linarith only [h3, h4, h727, hc23, hlam, hphi, u3elo3]
                    · linarith only [h715, h717, h718, h719, h720, h726, hc23, hlam, hphi, u3elo3]
                  · linarith only [h715, h717, h725, hc13, hlam, hphi, u3elo3]
              · linarith only [h4, h714, h719, h722, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h3, h4, h715, h719, hc12, hlam, hphi, ht23, u3elo3]
        · linarith only [h3, h4, h715, h717, h718, hc23, hlam, hphi, u3elo3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h735 | h735
        · rcases m.htr 1 2 3 (by decide) (by decide) with h736 | h736
          · rcases m.htr 1 2 4 (by decide) (by decide) with h737 | h737
            · linarith only [h1, h4, h737, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h739 | h739
              · rcases m.htr 1 3 4 (by decide) (by decide) with h740 | h740
                · linarith only [h0, h715, h717, h735, h740, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h742 | h742
                  · linarith only [h0, h717, h742, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h744 | h744
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h745 | h745
                      · linarith only [h715, h745, hc03, hlam, hphi, u3elo2]
                      · linarith only [h3, h4, h745, hc23, hlam, hphi, u3elo3]
                    · linarith only [h715, h735, h737, h744, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h4, h714, h736, h739, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h3, h4, h715, h736, hc12, hlam, hphi, ht23, u3elo3]
        · linarith only [h4, h714, h735, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h752 | h752
    · linarith only [h3, h4, h752, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h754 | h754
      · linarith only [h3, h714, h754, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h756 | h756
        · rcases m.htr 1 2 3 (by decide) (by decide) with h757 | h757
          · rcases m.htr 1 2 4 (by decide) (by decide) with h758 | h758
            · linarith only [h1, h4, h758, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h760 | h760
              · linarith only [h1, h3, h714, h752, h758, h760, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h762 | h762
                · linarith only [h0, h752, h754, h756, h762, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h764 | h764
                  · linarith only [h0, h754, h764, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h766 | h766
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h767 | h767
                      · linarith only [h3, h714, h752, h767, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · linarith only [h3, h4, h767, hc23, hlam, hphi, u3elo3]
                    · linarith only [h752, h756, h758, h766, hc12, hlam, hphi, ht23, u3elo3]
          · linarith only [h3, h4, h757, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h772 | h772
          · rcases m.htr 1 2 4 (by decide) (by decide) with h773 | h773
            · linarith only [h1, h3, h4, h752, h773, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h775 | h775
              · linarith only [h1, h3, h714, h754, h756, h773, h775, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h777 | h777
                · linarith only [h752, h777, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h779 | h779
                  · linarith only [h0, h3, h4, h754, h756, h779, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h781 | h781
                    · linarith only [h1, h756, h781, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h783 | h783
                      · linarith only [h752, h783, hc03, hlam, hphi, u3elo2]
                      · linarith only [h3, h4, h783, hc23, hlam, hphi, u3elo3]
          · linarith only [h3, h4, h772, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 6344000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 6344000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h787 | h787
  · rcases m.htr 0 2 5 (by decide) (by decide) with h788 | h788
    · rcases m.htr 0 3 4 (by decide) (by decide) with h789 | h789
      · rcases m.htr 0 3 5 (by decide) (by decide) with h790 | h790
        · rcases m.htr 0 4 5 (by decide) (by decide) with h791 | h791
          · rcases m.htr 1 2 3 (by decide) (by decide) with h792 | h792
            · linarith only [h0, h3, h792, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h794 | h794
              · rcases m.htr 1 2 5 (by decide) (by decide) with h795 | h795
                · rcases m.htr 1 3 4 (by decide) (by decide) with h796 | h796
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h797 | h797
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h798 | h798
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h799 | h799
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h800 | h800
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h801 | h801
                            · linarith only [h3, h787, h801, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                            · linarith only [h3, h787, h791, h799, h801, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                          · linarith only [h3, h800, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h3, h799, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h3, h787, h791, h798, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · linarith only [h3, h790, h797, hc13, hlam, hphi, u3elo2]
                  · linarith only [h3, h789, h792, h794, h796, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h3, h788, h794, h795, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h3, h787, h794, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h811 | h811
            · linarith only [h0, h3, h811, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h813 | h813
              · rcases m.htr 1 2 5 (by decide) (by decide) with h814 | h814
                · rcases m.htr 1 3 4 (by decide) (by decide) with h815 | h815
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h816 | h816
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h817 | h817
                      · linarith only [h1, h791, h817, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h819 | h819
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h820 | h820
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h821 | h821
                            · linarith only [h1, h3, h787, h791, h821, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h823 | h823
                              · linarith only [h1, h791, h813, h819, h823, hlam]
                              · rcases h5bigk with h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [hlam, p825_0]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h3, h788, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p825_1, u3elo2]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h3, h788, h820, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p825_1, u3elo2]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h3, h788, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p825_1, u3elo2]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h791, hlam, p825_1]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h2, hlam, p825_0]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [hlam, p825_0]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h2, h820, hc01, hc35, hlam, hphi, ht0b, ht5b, p825_1]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h2, h3, h788, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p825_1, u3elo2]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h817, hlam, p825_1]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h788, hlam, p825_1]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h814, hlam, p825_1]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [hlam, p825_0]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h3, h788, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p825_1, u3elo2]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h821, hlam, p825_1]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h790, hlam, p825_0]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h816, hlam, p825_0]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h820, hlam, p825_0]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [hlam, p825_0]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h823, hlam, p825_1]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h1, h791, h813, h819, hc34, hc45, hlam, hphi, p825_1]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h813, h817, h819, hc34, hc45, hlam, hphi, p825_1]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h819, h821, hc34, hc45, hlam, hphi, p825_1]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [h823, hc34, hc45, hlam, hphi, p825_1]
                                · have p825_0 := h825c.1
                                  have p825_1 := h825c.2.1
                                  have p825_2 := h825c.2.2.1
                                  have p825_3 := h825c.2.2.2
                                  linarith only [hlam, p825_0]
                          · linarith only [h3, h820, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h3, h787, h819, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h790, h811, h816, hc12, hlam, hphi, ht23, u3elo0]
                  · linarith only [h3, h789, h811, h813, h815, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h3, h788, h813, h814, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h3, h787, h813, hc12, hlam, hphi, ht23, u3elo2]
        · linarith only [h3, h788, h790, hlam]
      · linarith only [h3, h787, h789, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h859 | h859
      · rcases m.htr 0 3 5 (by decide) (by decide) with h860 | h860
        · rcases m.htr 0 4 5 (by decide) (by decide) with h861 | h861
          · linarith only [h787, h788, h861, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h863 | h863
            · linarith only [h0, h3, h863, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h865 | h865
              · rcases m.htr 1 2 5 (by decide) (by decide) with h866 | h866
                · linarith only [h788, h863, h866, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h868 | h868
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h869 | h869
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h870 | h870
                      · linarith only [h1, h861, h870, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h872 | h872
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h873 | h873
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h874 | h874
                            · linarith only [h787, h788, h861, h873, h874, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h876 | h876
                              · linarith only [h787, h788, h872, h874, h876, hlam]
                              · rcases h5bigk with h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [hlam, p878_0]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h788, h866, h873, hc12, hlam, hphi, ht23, p878_1, u3elo2]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h788, hlam, p878_0]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h788, h873, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p878_1, u3elo2]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h861, hlam, p878_1]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h2, hlam, p878_0]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [hlam, p878_0]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h866, hlam, p878_0]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p878_1]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h870, hlam, p878_1]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h873, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p878_1, u3elo2]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h873, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p878_1, u3elo2]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [hlam, p878_0]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h873, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p878_1, u3elo2]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h874, hlam, p878_1]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h860, hlam, p878_0]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h869, hlam, p878_0]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h873, hlam, p878_0]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [hlam, p878_0]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h876, hlam, p878_1]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h2, h865, h866, h872, hc34, hc45, hlam, hphi, p878_1]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h865, h866, h872, hc34, hc45, hlam, hphi, p878_1]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h787, h788, h872, hc34, hc45, hlam, hphi, p878_1]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [h876, hc34, hc45, hlam, hphi, p878_1]
                                · have p878_0 := h878c.1
                                  have p878_1 := h878c.2.1
                                  have p878_2 := h878c.2.2.1
                                  have p878_3 := h878c.2.2.2
                                  linarith only [hlam, p878_0]
                          · linarith only [h3, h787, h872, h873, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h863, h872, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h860, h869, hc13, hlam, hphi, u3elo0]
                  · linarith only [h3, h859, h863, h865, h868, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h787, h788, h865, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h909 | h909
          · linarith only [h787, h788, h909, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h911 | h911
            · linarith only [h0, h3, h860, h911, hc02, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h913 | h913
              · rcases m.htr 1 2 5 (by decide) (by decide) with h914 | h914
                · linarith only [h787, h788, h911, h914, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h916 | h916
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h917 | h917
                    · linarith only [h0, h860, h917, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h919 | h919
                      · linarith only [h1, h909, h919, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h921 | h921
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h922 | h922
                          · linarith only [h860, h922, hc03, hlam, hphi, u3elo2]
                          · linarith only [h3, h787, h921, h922, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h3, h787, h921, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h859, h860, h911, h916, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h3, h787, h913, hc12, hlam, hphi, ht23, u3elo2]
      · linarith only [h3, h787, h859, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h929 | h929
    · rcases m.htr 0 3 4 (by decide) (by decide) with h930 | h930
      · rcases m.htr 0 3 5 (by decide) (by decide) with h931 | h931
        · rcases m.htr 0 4 5 (by decide) (by decide) with h932 | h932
          · rcases m.htr 1 2 3 (by decide) (by decide) with h933 | h933
            · linarith only [h0, h3, h933, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h935 | h935
              · linarith only [h787, h929, h933, h935, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h937 | h937
                · rcases m.htr 1 3 4 (by decide) (by decide) with h938 | h938
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h939 | h939
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h940 | h940
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h941 | h941
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h942 | h942
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h943 | h943
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h944 | h944
                              · rcases h5bigk with h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [hlam, p945_0]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h787, h929, h937, h942, h944, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p945_1]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h3, h929, h942, h944, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p945_1, u3elo2]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h3, h929, h944, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p945_1, u3elo2]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h3, h929, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p945_1, u3elo2]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h2, hlam, p945_0]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [hlam, p945_0]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h2, h942, h944, hc01, hc45, hlam, hphi, ht0b, ht5b, p945_1]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h1, h935, h937, h944, hc01, hc45, hlam, hphi, ht0b, ht5b, p945_1]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h2, h3, h929, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p945_1, u3elo2]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h929, hlam, p945_1]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h937, hlam, p945_1]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [hlam, p945_0]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h3, h929, h944, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p945_1, u3elo2]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h787, h929, h941, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p945_1, u3elo2]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h931, hlam, p945_0]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h939, hlam, p945_0]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h942, hlam, p945_0]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [hlam, p945_0]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p945_1, u3elo4]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h932, hlam, p945_0]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h940, hlam, p945_0]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h943, hlam, p945_0]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [h944, hlam, p945_0]
                                · have p945_0 := h945c.1
                                  have p945_1 := h945c.2.1
                                  have p945_2 := h945c.2.2.1
                                  have p945_3 := h945c.2.2.2
                                  linarith only [hlam, p945_0]
                              · linarith only [h787, h929, h941, h943, h944, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · linarith only [h787, h929, h938, h940, h943, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h3, h929, h942, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                        · linarith only [h3, h929, h941, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h930, h932, h935, h940, hc12, hlam, hphi, ht23, u3elo0]
                    · linarith only [h3, h929, h931, h938, h939, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · linarith only [h3, h930, h938, hc13, hlam, hphi, u3elo2]
                · linarith only [h3, h929, h937, hc12, hlam, hphi, ht23, u3elo2]
          · linarith only [h787, h929, h932, hlam]
        · linarith only [h787, h929, h930, h931, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h981 | h981
        · rcases m.htr 0 4 5 (by decide) (by decide) with h982 | h982
          · rcases m.htr 1 2 3 (by decide) (by decide) with h983 | h983
            · linarith only [h0, h3, h929, h930, h983, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h985 | h985
              · linarith only [h787, h929, h983, h985, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h987 | h987
                · rcases m.htr 1 3 4 (by decide) (by decide) with h988 | h988
                  · linarith only [h0, h930, h988, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h990 | h990
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h991 | h991
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h992 | h992
                        · linarith only [h930, h992, hc03, hlam, hphi, u3elo2]
                        · linarith only [h3, h929, h992, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h930, h982, h983, h987, h988, h991, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h981, h983, h987, h990, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                · linarith only [h3, h929, h987, hc12, hlam, hphi, ht23, u3elo2]
          · linarith only [h787, h929, h982, hlam]
        · linarith only [h3, h929, h981, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1000 | h1000
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1001 | h1001
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1002 | h1002
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1003 | h1003
            · linarith only [h0, h1003, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1005 | h1005
              · linarith only [h1002, h1003, h1005, h787, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1007 | h1007
                · linarith only [h1005, h1007, h929, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1009 | h1009
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1010 | h1010
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1011 | h1011
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1012 | h1012
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1013 | h1013
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1014 | h1014
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1015 | h1015
                              · rcases h5bigk with h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [hlam, p1016_0]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h1002, h1007, h1012, h787, hc12, hlam, hphi, ht23, p1016_1, u3elo2]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h929, hlam, p1016_0]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h1001, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1016_1, u3elo2]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h1002, h1012, h787, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1016_1, u3elo2]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h2, hlam, p1016_0]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [hlam, p1016_0]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h1007, hlam, p1016_0]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p1016_1]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h1002, h1012, h2, h787, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1016_1, u3elo2]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h929, hc02, hc25, hlam, hphi, p1016_1]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h1007, hc12, hc25, hlam, hphi, p1016_1]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [hlam, p1016_0]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h1013, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1016_1, u3elo2]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h1012, h1014, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1016_1, u3elo2]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h1001, hlam, p1016_0]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h1010, hlam, p1016_0]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h1013, hlam, p1016_0]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [hlam, p1016_0]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1016_1, u3elo4]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h1002, hlam, p1016_0]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h1011, hlam, p1016_0]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h1014, hlam, p1016_0]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [h1015, hlam, p1016_0]
                                · have p1016_0 := h1016c.1
                                  have p1016_1 := h1016c.2.1
                                  have p1016_2 := h1016c.2.2.1
                                  have p1016_3 := h1016c.2.2.2
                                  linarith only [hlam, p1016_0]
                              · rcases h5bigk with h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [hlam, p1042_0]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h1011, h1015, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1042_1]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h929, hlam, p1042_0]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h1012, h1014, h929, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1042_1, u3elo2]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h1012, h1014, h1015, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1042_1, u3elo2]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h2, hlam, p1042_0]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [hlam, p1042_0]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h1007, hlam, p1042_0]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p1042_1]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h1012, h1014, h1015, h2, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1042_1, u3elo2]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h1012, h1014, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1042_1, u3elo2]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h1012, h1014, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1042_1, u3elo2]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [hlam, p1042_0]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h1012, h1014, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1042_1, u3elo2]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h1012, h1014, h1015, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1042_1, u3elo2]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h1001, hlam, p1042_0]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h1010, hlam, p1042_0]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h1013, hlam, p1042_0]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [hlam, p1042_0]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h1015, hlam, p1042_1]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h1002, hlam, p1042_0]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h1011, hlam, p1042_0]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h1014, hlam, p1042_0]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [h1011, h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p1042_1]
                                · have p1042_0 := h1042c.1
                                  have p1042_1 := h1042c.2.1
                                  have p1042_2 := h1042c.2.2.1
                                  have p1042_3 := h1042c.2.2.2
                                  linarith only [hlam, p1042_0]
                            · linarith only [h1, h1011, h1014, h787, hlam]
                          · linarith only [h1013, h3, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h1012, h3, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h1000, h1002, h1005, h1011, hc12, hlam, hphi, ht23, u3elo0]
                    · linarith only [h1001, h1010, h3, hc13, hlam, hphi, u3elo2]
                  · linarith only [h1000, h1003, h1009, h3, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1074 | h1074
            · linarith only [h0, h1074, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1076 | h1076
              · linarith only [h1074, h1076, h787, hc02, hlam, hphi, ht23, u3elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1078 | h1078
                · linarith only [h1074, h1078, h929, hc02, hlam, hphi, ht23, u3elo2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1080 | h1080
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1081 | h1081
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1082 | h1082
                      · linarith only [h1, h1002, h1082, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1084 | h1084
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1085 | h1085
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1086 | h1086
                            · linarith only [h1, h1002, h1076, h1084, h1086, hc12, hlam, hphi, ht23, u3elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1088 | h1088
                              · linarith only [h1086, h1088, h787, hc02, hlam, hphi, ht23, u3elo3]
                              · rcases h5bigk with h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [hlam, p1090_0]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h1085, h929, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1090_1, u3elo2]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h929, hlam, p1090_0]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h1085, h1088, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1090_1, u3elo2]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h1002, hlam, p1090_1]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h2, hlam, p1090_0]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [hlam, p1090_0]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h1078, hlam, p1090_0]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h1088, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1090_1]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h1082, hlam, p1090_1]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h1002, h1085, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1090_1, u3elo2]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h1085, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1090_1, u3elo2]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [hlam, p1090_0]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h1085, h1088, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1090_1, u3elo2]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h1086, hlam, p1090_1]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h1001, hlam, p1090_0]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h1081, hlam, p1090_0]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h1085, hlam, p1090_0]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [hlam, p1090_0]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h1088, hlam, p1090_1]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h1076, h1082, h2, hc12, hc45, hlam, hphi, ht23, ht34, p1090_1]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h1076, h1082, hc12, hc45, hlam, hphi, ht23, ht34, p1090_1]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h929, hc02, hc45, hlam, hphi, ht23, ht34, p1090_1]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [h1088, hc34, hc45, hlam, hphi, p1090_1]
                                · have p1090_0 := h1090c.1
                                  have p1090_1 := h1090c.2.1
                                  have p1090_2 := h1090c.2.2.1
                                  have p1090_3 := h1090c.2.2.2
                                  linarith only [hlam, p1090_0]
                          · linarith only [h0, h1081, h1085, hc23, hlam, hphi, u3elo0]
                        · linarith only [h1084, h3, hc02, hlam, hphi, ht23, u3elo3]
                    · linarith only [h1001, h1081, hc13, hlam, hphi, u3elo0]
                  · linarith only [h1000, h1074, h1080, h3, hc12, hlam, hphi, ht23, u3elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1120 | h1120
          · linarith only [h1000, h1001, h1120, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1122 | h1122
            · linarith only [h0, h1001, h1122, h3, hc02, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1124 | h1124
              · linarith only [h1122, h1124, h787, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1126 | h1126
                · linarith only [h1124, h1126, h929, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1128 | h1128
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1129 | h1129
                    · linarith only [h0, h1001, h1129, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1131 | h1131
                      · linarith only [h1, h1120, h1131, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1133 | h1133
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1134 | h1134
                          · linarith only [h1001, h1134, hc03, hlam, hphi, u3elo2]
                          · linarith only [h1134, h3, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h1133, h3, hc02, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1000, h1001, h1128, hc13, hlam, hphi, u3elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1139 | h1139
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1140 | h1140
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1141 | h1141
            · linarith only [h0, h1000, h1141, h3, hc02, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1143 | h1143
              · linarith only [h1141, h1143, h787, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1145 | h1145
                · linarith only [h1143, h1145, h929, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1147 | h1147
                  · linarith only [h0, h1000, h1147, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1149 | h1149
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1150 | h1150
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1151 | h1151
                        · linarith only [h1000, h1151, hc03, hlam, hphi, u3elo2]
                        · linarith only [h1151, h3, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h1000, h1139, h1140, h1143, h1150, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h1000, h1139, h1141, h1149, hc12, hlam, hphi, ht23, u3elo3]
          · linarith only [h1000, h1139, h1140, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1157 | h1157
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1158 | h1158
            · linarith only [h0, h1000, h1158, h3, hc02, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1160 | h1160
              · linarith only [h1158, h1160, h787, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1162 | h1162
                · linarith only [h1160, h1162, h929, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1164 | h1164
                  · linarith only [h0, h1000, h1164, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1166 | h1166
                    · linarith only [h0, h1139, h1166, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1168 | h1168
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1169 | h1169
                        · linarith only [h1000, h1169, hc03, hlam, hphi, u3elo2]
                        · linarith only [h1169, h3, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h1000, h1157, h1160, h1168, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1173 | h1173
            · linarith only [h0, h1173, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1175 | h1175
              · linarith only [h1173, h1175, h787, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1177 | h1177
                · linarith only [h1, h1157, h1175, h1177, h929, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1179 | h1179
                  · linarith only [h0, h1000, h1179, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1181 | h1181
                    · linarith only [h0, h1139, h1181, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1183 | h1183
                      · linarith only [h1, h1157, h1183, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1185 | h1185
                        · linarith only [h1000, h1185, hc03, hlam, hphi, u3elo2]
                        · linarith only [h1185, h3, hc02, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 6344000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3

set_option maxHeartbeats 6344000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1188 | h1188
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1189 | h1189
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1190 | h1190
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1191 | h1191
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1192 | h1192
          · linarith only [h0, h1192, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1194 | h1194
            · linarith only [h1, h1194, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1196 | h1196
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1197 | h1197
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1198 | h1198
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1199 | h1199
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1200 | h1200
                      · linarith only [h0, h1192, h1198, h1200, h2, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h1199, h1200, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h1191, h1199, hc13, hlam, hphi, u3elo0]
                  · linarith only [h1190, h1192, h1196, h1198, hc23, hlam, hphi, u3elo4]
                · linarith only [h1189, h1191, h1192, h1196, h1197, hc23, hlam, hphi, u3elo4]
              · linarith only [h1188, h1192, h1196, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1207 | h1207
          · linarith only [h0, h1191, h1207, h2, hc13, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1209 | h1209
            · linarith only [h1, h1209, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1211 | h1211
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1212 | h1212
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1213 | h1213
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1214 | h1214
                    · linarith only [h0, h1191, h1213, h1214, h2, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1216 | h1216
                      · linarith only [h0, h1191, h1207, h1216, h2, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h1, h1211, h1214, h1216, h2, hc23, hlam, hphi, u3elo4]
                  · linarith only [h1190, h1207, h1211, h1213, hc23, hlam, hphi, u3elo4]
                · linarith only [h1189, h1209, h1211, h1212, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h1188, h1191, h1211, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1222 | h1222
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1223 | h1223
          · linarith only [h0, h1223, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1225 | h1225
            · linarith only [h1, h1225, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1227 | h1227
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1228 | h1228
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1229 | h1229
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1230 | h1230
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1231 | h1231
                      · linarith only [h1223, h1231, hc03, hlam, hphi, u3elo1]
                      · linarith only [h0, h1230, h1231, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h1188, h1190, h1222, h1227, h1229, h1230, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1235 | h1235
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1236 | h1236
                      · linarith only [h0, h1223, h1236, h2, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h1235, h1236, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h0, h1222, h1223, h1227, h1235, h2, hc23, hlam, hphi, u3elo4]
                · linarith only [h1189, h1190, h1223, h1228, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h1188, h1190, h1223, h1227, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1242 | h1242
          · linarith only [h1188, h1190, h1222, h1242, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1244 | h1244
            · linarith only [h1, h1244, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1246 | h1246
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1247 | h1247
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1248 | h1248
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1249 | h1249
                    · linarith only [h1222, h1249, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1251 | h1251
                      · linarith only [h0, h1222, h1242, h1251, h2, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h1, h1246, h1249, h1251, h2, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1254 | h1254
                    · linarith only [h0, h1222, h1254, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1256 | h1256
                      · linarith only [h1, h1242, h1254, h1256, h2, hlam]
                      · linarith only [h1, h1254, h1256, h2, hc13, hlam, hphi, u3elo4]
                · linarith only [h1189, h1190, h1247, hc12, hc25, hlam, hphi]
              · linarith only [h1188, h1222, h1246, hc12, hlam, hphi, ht23, u3elo3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1261 | h1261
      · linarith only [h1, h1189, h1261, h2, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1263 | h1263
        · linarith only [h1188, h1189, h1263, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1265 | h1265
          · linarith only [h1, h1188, h1189, h1265, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1267 | h1267
            · linarith only [h1, h1267, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1269 | h1269
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1270 | h1270
                · linarith only [h1, h1188, h1189, h1270, h2, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h1, h1265, h1269, h1270, h2, hc23, hlam, hphi, u3elo4]
              · linarith only [h1188, h1189, h1269, hc12, hc24, hlam, hphi]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1274 | h1274
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1275 | h1275
      · linarith only [h0, h1188, h1275, h2, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1277 | h1277
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1278 | h1278
          · linarith only [h0, h1278, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1280 | h1280
            · linarith only [h0, h1188, h1274, h1280, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1282 | h1282
              · linarith only [h0, h1188, h1274, h1278, h1282, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1284 | h1284
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1285 | h1285
                  · linarith only [h1275, h1282, h1285, h2, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1287 | h1287
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1288 | h1288
                      · linarith only [h0, h1278, h1288, h2, hlam]
                      · linarith only [h0, h1282, h1284, h1288, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h1277, h1282, h1284, h1287, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                · linarith only [h1188, h1274, h1284, hc12, hlam, hphi, ht23, u3elo2]
        · linarith only [h1188, h1274, h1277, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1294 | h1294
      · linarith only [h1, h1274, h1294, h2, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1296 | h1296
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1297 | h1297
          · linarith only [h0, h1297, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1299 | h1299
            · linarith only [h0, h1296, h1299, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1301 | h1301
              · linarith only [h0, h1188, h1297, h1301, hc02, hlam, hphi, ht23, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1303 | h1303
                · linarith only [h1274, h1301, h1303, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1305 | h1305
                  · linarith only [h0, h1294, h1301, h1305, h2, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1307 | h1307
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1308 | h1308
                      · linarith only [h0, h1297, h1308, h2, hlam]
                      · linarith only [h0, h1307, h1308, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h1296, h1297, h1301, h1307, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1312 | h1312
          · linarith only [h0, h1296, h1312, h2, hc13, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1314 | h1314
            · linarith only [h1, h1314, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1316 | h1316
              · linarith only [h0, h1188, h1296, h1316, hc02, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1318 | h1318
                · linarith only [h1274, h1316, h1318, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1320 | h1320
                  · linarith only [h1294, h1318, h1320, hc02, hc24, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1322 | h1322
                    · linarith only [h0, h1296, h1322, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1324 | h1324
                      · linarith only [h0, h1296, h1312, h1324, h2, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h1, h1316, h1322, h1324, h2, hc12, hlam, hphi, ht23, u3elo4]

set_option maxHeartbeats 6344000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2

set_option maxHeartbeats 6344000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1327 | h1327
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1328 | h1328
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1329 | h1329
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1330 | h1330
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1331 | h1331
          · linarith only [h0, h1, h1331, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1333 | h1333
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1334 | h1334
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1335 | h1335
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1336 | h1336
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1337 | h1337
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1338 | h1338
                      · linarith only [h0, h1, h1331, h1336, h1338, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h1, h1338, hc13, hlam, hphi, u3elo3]
                    · linarith only [h1330, h1331, h1333, h1337, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1329, h1331, h1335, h1336, hc23, hlam, hphi, u3elo3]
                · linarith only [h1328, h1331, h1335, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h0, h1, h1331, h1333, h1334, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1345 | h1345
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1346 | h1346
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1347 | h1347
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1348 | h1348
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1349 | h1349
                      · linarith only [h0, h1, h1331, h1347, h1349, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h1, h1346, h1349, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1, h1330, h1346, h1347, h1348, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h1329, h1331, h1346, h1347, hc23, hlam, hphi, u3elo3]
                · linarith only [h1328, h1331, h1346, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h1, h1327, h1345, hlam]
        · linarith only [h1, h1327, h1329, h1330, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1357 | h1357
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1358 | h1358
          · linarith only [h0, h1, h1358, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1360 | h1360
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1361 | h1361
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1362 | h1362
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1363 | h1363
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1364 | h1364
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1365 | h1365
                      · linarith only [h0, h1358, h1360, h1365, hc01, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h1, h1365, hc13, hlam, hphi, u3elo3]
                    · linarith only [h1329, h1357, h1363, h1364, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1369 | h1369
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1370 | h1370
                      · linarith only [h0, h1, h1358, h1370, hlam]
                      · linarith only [h0, h1, h1370, hc13, hlam, hphi, u3elo3]
                    · linarith only [h1329, h1357, h1369, hc12, hc24, hlam, hphi]
                · linarith only [h1328, h1329, h1358, h1362, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h0, h1, h1360, h1361, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1376 | h1376
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1377 | h1377
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1378 | h1378
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1379 | h1379
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1380 | h1380
                      · linarith only [h0, h1, h1358, h1380, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h1, h1377, h1380, hc23, hlam, hphi, u3elo3]
                    · linarith only [h1329, h1357, h1378, h1379, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1384 | h1384
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1385 | h1385
                      · linarith only [h0, h1, h1358, h1376, h1385, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h1, h1385, hc13, hlam, hphi, u3elo3]
                    · linarith only [h1329, h1357, h1384, hc12, hc24, hlam, hphi]
                · linarith only [h1328, h1329, h1358, h1377, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h1, h1327, h1376, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1391 | h1391
          · linarith only [h0, h1, h1391, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1393 | h1393
            · linarith only [h1328, h1357, h1391, h1393, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1395 | h1395
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1396 | h1396
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1397 | h1397
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1398 | h1398
                    · linarith only [h1, h1327, h1328, h1357, h1398, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1328, h1329, h1397, h1398, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1401 | h1401
                    · linarith only [h1328, h1357, h1397, h1401, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h1, h1327, h1391, h1396, h1401, hc23, hlam, hphi, u3elo3]
                · linarith only [h1328, h1357, h1396, hc12, hc25, hlam, hphi]
              · linarith only [h1, h1327, h1395, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1406 | h1406
      · linarith only [h0, h1, h1328, h1406, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1408 | h1408
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1409 | h1409
          · linarith only [h0, h1, h1409, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1411 | h1411
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1412 | h1412
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1413 | h1413
                · linarith only [h0, h1328, h1409, h1413, hc02, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1415 | h1415
                  · linarith only [h1, h1406, h1413, h1415, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1417 | h1417
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1418 | h1418
                      · linarith only [h0, h1, h1409, h1418, hlam]
                      · linarith only [h0, h1, h1413, h1417, h1418, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h1328, h1408, h1417, hc12, hlam, hphi, ht23, u3elo2]
              · linarith only [h0, h1, h1328, h1408, h1412, hlam]
            · linarith only [h1328, h1408, h1411, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1424 | h1424
          · linarith only [h0, h1, h1424, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1426 | h1426
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1427 | h1427
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1428 | h1428
                · linarith only [h0, h1328, h1424, h1428, hc02, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1430 | h1430
                  · linarith only [h1406, h1428, h1430, hc02, hc23, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1432 | h1432
                    · linarith only [h0, h1, h1408, h1424, h1428, h1432, hc02, hlam, hphi, ht23, u3elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1434 | h1434
                      · linarith only [h0, h1, h1424, h1434, hlam]
                      · linarith only [h0, h1, h1428, h1434, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h0, h1, h1424, h1426, h1427, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1438 | h1438
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1439 | h1439
                · linarith only [h0, h1328, h1424, h1439, hc02, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1441 | h1441
                  · linarith only [h1, h1406, h1439, h1441, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1443 | h1443
                    · linarith only [h0, h1, h1408, h1439, h1443, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1445 | h1445
                      · linarith only [h0, h1, h1424, h1445, hlam]
                      · linarith only [h0, h1, h1439, h1445, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h1, h1327, h1438, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1449 | h1449
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1450 | h1450
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1451 | h1451
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1452 | h1452
          · linarith only [h0, h1, h1452, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1454 | h1454
            · linarith only [h0, h1327, h1452, h1454, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1456 | h1456
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1457 | h1457
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1458 | h1458
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1459 | h1459
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1460 | h1460
                      · linarith only [h0, h1, h1452, h1458, h1460, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h1, h1457, h1460, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1, h1451, h1457, h1458, h1459, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h1450, h1452, h1457, h1458, hc23, hlam, hphi, u3elo3]
                · linarith only [h1449, h1452, h1457, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1466 | h1466
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1467 | h1467
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1468 | h1468
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1469 | h1469
                      · linarith only [h0, h1, h1452, h1469, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h1, h1469, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h1, h1451, h1466, h1467, h1468, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h1450, h1454, h1456, h1466, h1467, hc23, hlam, hphi, u3elo4]
                · linarith only [h1449, h1452, h1466, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1475 | h1475
          · linarith only [h0, h1, h1475, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1477 | h1477
            · linarith only [h0, h1327, h1475, h1477, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1479 | h1479
              · linarith only [h1450, h1451, h1479, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1481 | h1481
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1482 | h1482
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1483 | h1483
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1484 | h1484
                      · linarith only [h0, h1, h1475, h1484, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h1, h1481, h1484, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1487 | h1487
                      · linarith only [h0, h1475, h1487, hlam]
                      · linarith only [h0, h1, h1481, h1487, hc23, hlam, hphi, u3elo3]
                  · linarith only [h1450, h1451, h1477, h1482, hc12, hlam, hphi, ht23, u3elo4]
                · linarith only [h1449, h1451, h1477, h1481, hc12, hlam, hphi, ht23, u3elo4]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1492 | h1492
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1493 | h1493
          · linarith only [h0, h1, h1493, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1495 | h1495
            · linarith only [h0, h1327, h1495, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1497 | h1497
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1498 | h1498
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1499 | h1499
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1500 | h1500
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1501 | h1501
                      · linarith only [h0, h1327, h1450, h1492, h1493, h1499, h1501, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h1327, h1450, h1492, h1498, h1499, h1501, hc23, hlam, hphi, u3elo3]
                    · linarith only [h1450, h1492, h1499, h1500, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1505 | h1505
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1506 | h1506
                      · linarith only [h0, h1327, h1499, h1505, h1506, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h1327, h1499, h1505, h1506, hc13, hlam, hphi, u3elo3]
                    · linarith only [h1450, h1492, h1505, hc12, hc24, hlam, hphi]
                · linarith only [h1449, h1450, h1493, h1498, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h1450, h1492, h1497, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1512 | h1512
          · linarith only [h0, h1, h1512, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1514 | h1514
            · linarith only [h0, h1327, h1514, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1516 | h1516
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1517 | h1517
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1518 | h1518
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1519 | h1519
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1520 | h1520
                      · linarith only [h1512, h1520, hc03, hlam, hphi, u3elo1]
                      · linarith only [h0, h1, h1517, h1520, hc23, hlam, hphi, u3elo3]
                    · linarith only [h1450, h1518, h1519, hc02, hc25, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1524 | h1524
                    · linarith only [h1449, h1492, h1518, h1524, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1526 | h1526
                      · linarith only [h0, h1512, h1526, hlam]
                      · linarith only [h0, h1, h1526, hc13, hlam, hphi, u3elo3]
                · linarith only [h1449, h1450, h1517, hc12, hc24, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1530 | h1530
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1531 | h1531
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1532 | h1532
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1533 | h1533
                      · linarith only [h0, h1, h1516, h1533, hc34, hc45, hlam, hphi]
                      · linarith only [h0, h1, h1533, hc13, hlam, hphi, u3elo3]
                    · linarith only [h1450, h1531, h1532, hc02, hc25, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1537 | h1537
                    · linarith only [h1449, h1492, h1531, h1537, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1539 | h1539
                      · linarith only [h0, h1, h1516, h1539, hc34, hc45, hlam, hphi]
                      · linarith only [h0, h1, h1530, h1539, hc23, hlam, hphi, u3elo3]
                · linarith only [h1449, h1450, h1530, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1543 | h1543
      · linarith only [h0, h1, h1449, h1543, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1545 | h1545
        · linarith only [h0, h1327, h1449, h1545, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1547 | h1547
          · linarith only [h0, h1, h1547, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1549 | h1549
            · linarith only [h0, h1327, h1549, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1551 | h1551
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1552 | h1552
                · linarith only [h0, h1449, h1547, h1552, hc02, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1554 | h1554
                  · linarith only [h1327, h1543, h1551, h1552, h1554, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1556 | h1556
                    · linarith only [h0, h1327, h1545, h1552, h1556, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1558 | h1558
                      · linarith only [h0, h1327, h1547, h1551, h1558, hlam]
                      · linarith only [h0, h1, h1552, h1558, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1561 | h1561
                · linarith only [h0, h1, h1449, h1549, h1551, h1561, hc02, hlam, hphi, ht23, u3elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1563 | h1563
                  · linarith only [h1543, h1561, h1563, hc02, hc23, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1565 | h1565
                    · linarith only [h0, h1, h1545, h1549, h1551, h1561, h1565, hc02, hlam, hphi, ht23, u3elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1567 | h1567
                      · linarith only [h0, h1, h1551, h1567, hc34, hc45, hlam, hphi]
                      · linarith only [h0, h1, h1561, h1567, hc12, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 6344000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0_x0 m hb0 hb2 hb3 hb5 h0 h1
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0_x1 m hb0 hb2 hb3 hb5 h0 h1

end R2N4
