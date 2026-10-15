import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_43S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h754 | h754
  · rcases m.htr 0 3 5 (by decide) (by decide) with h755 | h755
    · linarith only [h4, h6, h755, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h757 | h757
      · linarith only [h5, h6, h757, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h759 | h759
        · rcases m.htr 1 2 5 (by decide) (by decide) with h760 | h760
          · linarith only [h0, h6, h760, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h762 | h762
            · rcases m.htr 1 4 5 (by decide) (by decide) with h763 | h763
              · linarith only [h0, h2, h6, h754, h755, h757, h759, h763, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h765 | h765
                · rcases m.htr 2 3 5 (by decide) (by decide) with h766 | h766
                  · linarith only [h0, h6, h755, h759, h766, hlam]
                  · linarith only [h0, h6, h759, h765, h766, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · linarith only [h1, h762, h765, hc23, hlam, hphi, u3elo0]
            · linarith only [h754, h755, h762, hc13, hlam, hphi, u3elo4]
        · linarith only [h4, h6, h759, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h772 | h772
    · linarith only [h4, h6, h754, h772, hc23, hlam, hphi, u3elo3]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h774 | h774
      · linarith only [h5, h6, h774, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h776 | h776
        · rcases m.htr 1 2 5 (by decide) (by decide) with h777 | h777
          · linarith only [h0, h6, h777, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h779 | h779
            · linarith only [h754, h779, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h781 | h781
              · linarith only [h2, h774, h781, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h783 | h783
                · linarith only [h1, h754, h776, h783, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h785 | h785
                  · linarith only [h0, h6, h772, h776, h785, hlam]
                  · linarith only [h0, h6, h776, h785, hc23, hlam, hphi, u3elo4]
        · linarith only [h4, h6, h776, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0_x0_x0_x0_x0 m hb0 hb3 hb4 h0 h1 h2 h3 h4 h5 h6
  · exact r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0_x0_x0_x0_x1 m hb0 hb3 hb4 h0 h1 h2 h3 h4 h5 h6

set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h789 | h789
  · rcases m.htr 0 3 4 (by decide) (by decide) with h790 | h790
    · linarith only [h4, h5, h790, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h792 | h792
      · rcases m.htr 0 4 5 (by decide) (by decide) with h793 | h793
        · rcases m.htr 1 2 3 (by decide) (by decide) with h794 | h794
          · rcases m.htr 1 2 5 (by decide) (by decide) with h795 | h795
            · rcases m.htr 1 3 4 (by decide) (by decide) with h796 | h796
              · linarith only [h1, h790, h796, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h798 | h798
                · rcases m.htr 2 3 4 (by decide) (by decide) with h799 | h799
                  · linarith only [h0, h1, h5, h790, h794, h799, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h4, h5, h799, hc23, hlam, hphi, u3elo3]
                · linarith only [h790, h792, h793, h796, h798, hc13, hlam, hphi, u3elo3]
            · linarith only [h5, h789, h794, h795, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h4, h5, h790, h794, hc12, hlam, hphi, ht23, u3elo3]
        · linarith only [h4, h5, h790, h792, h793, hc23, hlam, hphi, u3elo3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h806 | h806
        · rcases m.htr 1 2 3 (by decide) (by decide) with h807 | h807
          · rcases m.htr 1 2 5 (by decide) (by decide) with h808 | h808
            · rcases m.htr 1 3 4 (by decide) (by decide) with h809 | h809
              · linarith only [h1, h790, h809, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h811 | h811
                · rcases m.htr 2 3 4 (by decide) (by decide) with h812 | h812
                  · linarith only [h0, h5, h790, h807, h812, hlam]
                  · linarith only [h0, h5, h807, h812, hc23, hlam, hphi, u3elo3]
                · linarith only [h790, h806, h807, h809, h811, hc23, hlam, hphi, u3elo3]
            · linarith only [h5, h789, h807, h808, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h4, h5, h790, h807, hc12, hlam, hphi, ht23, u3elo3]
        · linarith only [h5, h789, h806, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h819 | h819
    · linarith only [h4, h5, h819, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h821 | h821
      · linarith only [h4, h789, h821, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h823 | h823
        · rcases m.htr 1 2 3 (by decide) (by decide) with h824 | h824
          · rcases m.htr 1 2 5 (by decide) (by decide) with h825 | h825
            · linarith only [h0, h789, h825, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h827 | h827
              · linarith only [h1, h819, h827, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h829 | h829
                · rcases m.htr 2 3 4 (by decide) (by decide) with h830 | h830
                  · linarith only [h0, h1, h789, h819, h824, h830, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h4, h5, h830, hc23, hlam, hphi, u3elo3]
                · linarith only [h819, h823, h824, h827, h829, hc23, hlam, hphi, u3elo3]
          · linarith only [h4, h5, h824, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h835 | h835
          · rcases m.htr 1 2 5 (by decide) (by decide) with h836 | h836
            · linarith only [h0, h789, h836, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h838 | h838
              · linarith only [h1, h819, h838, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h840 | h840
                · linarith only [h0, h2, h5, h823, h835, h840, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h842 | h842
                  · linarith only [h0, h1, h789, h819, h835, h842, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h4, h5, h842, hc23, hlam, hphi, u3elo3]
          · linarith only [h4, h5, h835, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0_x0_x0_x0 m hb0 hb3 hb4 h0 h1 h2 h3 h4 h5
  · exact r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0_x0_x0_x1 m hb0 hb3 hb4 h0 h1 h2 h3 h4 h5

set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h846 | h846
  · rcases m.htr 0 2 5 (by decide) (by decide) with h847 | h847
    · rcases m.htr 0 3 4 (by decide) (by decide) with h848 | h848
      · rcases m.htr 0 3 5 (by decide) (by decide) with h849 | h849
        · rcases m.htr 0 4 5 (by decide) (by decide) with h850 | h850
          · rcases m.htr 1 2 3 (by decide) (by decide) with h851 | h851
            · linarith only [h0, h4, h846, h851, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h853 | h853
              · rcases m.htr 1 3 4 (by decide) (by decide) with h854 | h854
                · rcases m.htr 1 4 5 (by decide) (by decide) with h855 | h855
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h856 | h856
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h857 | h857
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h858 | h858
                        · linarith only [h4, h846, h858, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                        · linarith only [h4, h846, h850, h856, h858, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · linarith only [h4, h857, hc02, hlam, hphi, ht23, u3elo4]
                    · linarith only [h4, h856, hc02, hlam, hphi, ht23, u3elo3]
                  · linarith only [h4, h846, h850, h854, h855, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h848, h854, hc13, hlam, hphi, u3elo0]
              · linarith only [h4, h847, h853, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h866 | h866
            · linarith only [h0, h4, h847, h866, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h868 | h868
              · rcases m.htr 1 3 4 (by decide) (by decide) with h869 | h869
                · rcases m.htr 1 4 5 (by decide) (by decide) with h870 | h870
                  · linarith only [h2, h850, h870, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h872 | h872
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h873 | h873
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h874 | h874
                        · linarith only [h4, h846, h850, h874, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h876 | h876
                          · linarith only [h0, h4, h850, h868, h872, h874, h876, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                          · rcases h0bigk with h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c | h878c
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [hlam, p878_0]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [h0, h868, h874, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p878_1]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [h1, h866, h868, h872, h874, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p878_1]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              rcases p878_3 (m.d 0 1) (by simp) with h882 | h882
                              · rcases p878_3 (m.d 0 2) (by simp) with h883 | h883
                                · linarith only [h0, h883, hlam]
                                · linarith only [h846, h883, hlam]
                              · linarith only [h2, h882, hlam]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              rcases p878_3 (m.d 0 1) (by simp) with h887 | h887
                              · rcases p878_3 (m.d 0 2) (by simp) with h888 | h888
                                · linarith only [h0, h888, hlam]
                                · linarith only [h847, h888, hlam]
                              · linarith only [h3, h887, hlam]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [h0, hlam, p878_0]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [hlam, p878_0]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [h4, hlam, p878_0]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [h4, h846, h872, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p878_1, u3elo2]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [h3, h4, h868, h872, h874, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p878_1, u3elo0]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [h1, hlam, p878_1]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [hc02, hlam, hphi, ht23, p878_1, u3elo0]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [hlam, p878_0]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [h4, h846, h872, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p878_1, u3elo2]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [h3, h4, h868, h872, h874, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p878_1, u3elo2]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [h2, hlam, p878_0]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [h846, hlam, p878_0]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [h848, hlam, p878_0]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [hlam, p878_0]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [h850, hlam, p878_0]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [h3, hlam, p878_0]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [h847, hlam, p878_1]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [h849, hlam, p878_0]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [h4, h846, h847, h872, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p878_1, u3elo2]
                            · have p878_0 := h878c.1
                              have p878_1 := h878c.2.1
                              have p878_2 := h878c.2.2.1
                              have p878_3 := h878c.2.2.2
                              linarith only [hlam, p878_0]
                      · linarith only [h4, h873, hc02, hlam, hphi, ht23, u3elo4]
                    · linarith only [h0, h4, h868, h872, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h4, h846, h848, h866, h868, h869, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · linarith only [h4, h847, h868, hc12, hlam, hphi, ht23, u3elo2]
        · linarith only [h4, h847, h849, hlam]
      · linarith only [h4, h846, h848, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h918 | h918
      · rcases m.htr 0 3 5 (by decide) (by decide) with h919 | h919
        · rcases m.htr 0 4 5 (by decide) (by decide) with h920 | h920
          · linarith only [h846, h847, h920, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h922 | h922
            · linarith only [h0, h4, h922, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h924 | h924
              · linarith only [h847, h922, h924, hc02, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h926 | h926
                · rcases m.htr 1 4 5 (by decide) (by decide) with h927 | h927
                  · linarith only [h2, h846, h847, h920, h927, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h929 | h929
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h930 | h930
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h931 | h931
                        · linarith only [h846, h847, h920, h930, h931, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h933 | h933
                          · linarith only [h847, h931, h933, hc02, hlam, hphi, ht23, u3elo3]
                          · rcases h0bigk with h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h846, h929, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p935_1]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h846, h847, h919, h929, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p935_1]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              rcases p935_3 (m.d 0 1) (by simp) with h939 | h939
                              · rcases p935_3 (m.d 0 2) (by simp) with h940 | h940
                                · linarith only [h0, h940, hlam]
                                · linarith only [h846, h940, hlam]
                              · linarith only [h2, h939, hlam]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h846, h847, h929, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p935_1]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h0, hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h4, hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h846, h847, h929, h930, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p935_1]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h847, hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h1, hlam, p935_1]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [hc02, hlam, hphi, ht23, p935_1, u3elo0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h4, h846, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p935_1, u3elo2]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h4, h846, h847, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p935_1, u3elo2]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h2, hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h846, hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h918, hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h920, hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h3, hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h846, h929, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p935_1]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h919, hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h846, h847, h929, h930, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p935_1, u3elo2]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [hlam, p935_0]
                      · linarith only [h4, h846, h929, h930, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h4, h929, hc02, hlam, hphi, ht23, u3elo3]
                · linarith only [h4, h846, h918, h926, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h968 | h968
          · linarith only [h846, h847, h968, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h970 | h970
            · linarith only [h0, h4, h970, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h972 | h972
              · linarith only [h846, h847, h970, h972, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h974 | h974
                · rcases m.htr 1 4 5 (by decide) (by decide) with h975 | h975
                  · linarith only [h2, h968, h975, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h977 | h977
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h978 | h978
                      · linarith only [h919, h978, hc03, hlam, hphi, u3elo2]
                      · linarith only [h4, h846, h977, h978, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h4, h846, h977, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · linarith only [h918, h919, h974, hc13, hlam, hphi, u3elo4]
      · linarith only [h4, h846, h918, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h984 | h984
    · rcases m.htr 0 3 4 (by decide) (by decide) with h985 | h985
      · rcases m.htr 0 3 5 (by decide) (by decide) with h986 | h986
        · rcases m.htr 0 4 5 (by decide) (by decide) with h987 | h987
          · rcases m.htr 1 2 3 (by decide) (by decide) with h988 | h988
            · linarith only [h0, h4, h988, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h990 | h990
              · rcases m.htr 1 3 4 (by decide) (by decide) with h991 | h991
                · rcases m.htr 1 4 5 (by decide) (by decide) with h992 | h992
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h993 | h993
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h994 | h994
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h995 | h995
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h996 | h996
                          · rcases h0bigk with h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [hlam, p997_0]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h0, h990, h994, h996, hc01, hc45, hlam, hphi, ht0b, ht5b, p997_1]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h1, h991, h996, hc01, hc45, hlam, hphi, ht0b, ht5b, p997_1]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h2, h991, h996, hc01, hc45, hlam, hphi, ht0b, ht5b, p997_1]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              rcases p997_3 (m.d 0 1) (by simp) with h1002 | h1002
                              · rcases p997_3 (m.d 0 2) (by simp) with h1003 | h1003
                                · linarith only [h0, h1003, hlam]
                                · linarith only [h1003, h984, hlam]
                              · linarith only [h1002, h3, hlam]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h0, hlam, p997_0]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [hlam, p997_0]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h4, hlam, p997_0]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h846, hlam, p997_1]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h3, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p997_1, u3elo2]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h1, hlam, p997_1]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [hc02, hlam, hphi, ht23, p997_1, u3elo0]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [hlam, p997_0]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h0, h4, h846, h990, h994, h996, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p997_1, u3elo2]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h4, h984, h994, h996, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p997_1, u3elo2]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h2, hlam, p997_0]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h0, h990, h994, h996, hc04, hc45, hlam, hphi, ht0b, ht5b, p997_1]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h985, hlam, p997_0]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [hlam, p997_0]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h846, h984, h993, h994, h996, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p997_1, u3elo2]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h3, hlam, p997_0]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h984, hlam, p997_1]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h986, hlam, p997_0]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [h987, hlam, p997_1]
                            · have p997_0 := h997c.1
                              have p997_1 := h997c.2.1
                              have p997_2 := h997c.2.2.1
                              have p997_3 := h997c.2.2.2
                              linarith only [hlam, p997_0]
                          · linarith only [h846, h984, h993, h995, h996, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · linarith only [h0, h846, h990, h991, h992, h995, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h846, h993, h994, hc02, hlam, hphi, ht23, u3elo4]
                    · linarith only [h0, h4, h990, h993, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1031 | h1031
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1032 | h1032
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1033 | h1033
                        · linarith only [h0, h1031, h1033, h846, h990, h991, h992, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · linarith only [h0, h1033, h846, h985, h987, h990, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h1031, h1032, h846, h984, h987, h991, h992, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h1031, h4, h991, hc03, hlam, hphi, u3elo1]
                · linarith only [h985, h991, hc13, hlam, hphi, u3elo0]
              · linarith only [h846, h984, h990, hc12, hc24, hlam, hphi]
          · linarith only [h846, h984, h987, hlam]
        · linarith only [h846, h984, h985, h986, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1042 | h1042
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1043 | h1043
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1044 | h1044
            · linarith only [h0, h1044, h4, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1046 | h1046
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1047 | h1047
                · linarith only [h1047, h4, h985, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1049 | h1049
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1050 | h1050
                    · linarith only [h0, h1046, h1050, h4, h985, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h0, h1046, h1050, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h1043, h1047, h1049, h4, h984, hc13, hlam, hphi, u3elo2]
              · linarith only [h1046, h4, h984, h985, hc12, hlam, hphi, ht23, u3elo3]
          · linarith only [h1043, h846, h984, hlam]
        · linarith only [h1042, h4, h984, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1057 | h1057
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1058 | h1058
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1059 | h1059
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1060 | h1060
            · linarith only [h0, h1060, h4, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1062 | h1062
              · linarith only [h0, h1062, h984, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1064 | h1064
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1065 | h1065
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1066 | h1066
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1067 | h1067
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1068 | h1068
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1069 | h1069
                          · rcases h0bigk with h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [hlam, p1070_0]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              rcases p1070_3 (m.d 0 1) (by simp) with h1072 | h1072
                              · rcases p1070_3 (m.d 0 2) (by simp) with h1073 | h1073
                                · linarith only [h0, h1073, hlam]
                                · rcases p1070_3 (m.d 0 3) (by simp) with h1075 | h1075
                                  · linarith only [h1, h1075, hlam]
                                  · linarith only [h1075, h4, hlam]
                              · linarith only [h0, h1072, hlam]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h1, h1064, h1069, hc01, hc45, hlam, hphi, ht0b, ht5b, p1070_1]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h1064, h1069, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1070_1]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              rcases p1070_3 (m.d 0 1) (by simp) with h1081 | h1081
                              · rcases p1070_3 (m.d 0 2) (by simp) with h1082 | h1082
                                · linarith only [h0, h1082, hlam]
                                · rcases p1070_3 (m.d 0 3) (by simp) with h1084 | h1084
                                  · linarith only [h1, h1084, hlam]
                                  · linarith only [h1058, h1084, hlam]
                              · linarith only [h1081, h3, hlam]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h0, hlam, p1070_0]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [hlam, p1070_0]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h4, hlam, p1070_0]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h846, hlam, p1070_1]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h984, hlam, p1070_0]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h1, hlam, p1070_1]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h0, h4, hc12, hc23, hlam, hphi, p1070_1]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [hlam, p1070_0]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h1064, h1069, h2, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1070_1, u3elo2]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h0, h4, h984, hc12, hlam, hphi, ht23, p1070_1, u3elo2]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h2, hlam, p1070_0]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h0, h1066, h846, hc12, hlam, hphi, ht23, p1070_1, u3elo2]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h1057, hlam, p1070_0]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [hlam, p1070_0]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h0, h1066, h846, h984, hc12, hlam, hphi, ht23, p1070_1, u3elo2]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h3, hlam, p1070_0]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h0, h1066, h1068, h984, hc12, hlam, hphi, ht23, p1070_1, u3elo2]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h1058, hlam, p1070_0]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [h1059, hlam, p1070_1]
                            · have p1070_0 := h1070c.1
                              have p1070_1 := h1070c.2.1
                              have p1070_2 := h1070c.2.2.1
                              have p1070_3 := h1070c.2.2.2
                              linarith only [hlam, p1070_0]
                          · rcases h0bigk with h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c | h1108c
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [hlam, p1108_0]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              rcases p1108_3 (m.d 0 1) (by simp) with h1110 | h1110
                              · rcases p1108_3 (m.d 0 2) (by simp) with h1111 | h1111
                                · linarith only [h0, h1111, hlam]
                                · rcases p1108_3 (m.d 0 3) (by simp) with h1113 | h1113
                                  · linarith only [h1, h1113, hlam]
                                  · linarith only [h1113, h4, hlam]
                              · linarith only [h0, h1110, hlam]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h1, h1064, h1065, h1069, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1108_1]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h1065, h1069, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1108_1]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h1059, h1069, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1108_1]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h0, hlam, p1108_0]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [hlam, p1108_0]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h4, hlam, p1108_0]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h846, hlam, p1108_1]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h984, hlam, p1108_0]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h1, hlam, p1108_1]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, p1108_1, u3elo0]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [hlam, p1108_0]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h1065, h1069, h2, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1108_1, u3elo2]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h0, h4, h984, hc12, hlam, hphi, ht23, p1108_1, u3elo2]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h2, hlam, p1108_0]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h0, h846, hc12, hc24, hlam, hphi, p1108_1]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h1057, hlam, p1108_0]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [hlam, p1108_0]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h0, h1057, h4, h984, hc12, hlam, hphi, ht23, p1108_1, u3elo2]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h3, hlam, p1108_0]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h0, h1068, h984, hc12, hc24, hlam, hphi, p1108_1]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h1058, hlam, p1108_0]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [h1059, hlam, p1108_1]
                            · have p1108_0 := h1108c.1
                              have p1108_1 := h1108c.2.1
                              have p1108_2 := h1108c.2.2.1
                              have p1108_3 := h1108c.2.2.2
                              linarith only [hlam, p1108_0]
                        · linarith only [h0, h1064, h1065, h1068, h846, hc12, hlam, hphi, ht23, u3elo1]
                      · linarith only [h1058, h1067, h4, hlam]
                    · linarith only [h0, h1066, h4, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1143 | h1143
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1144 | h1144
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1145 | h1145
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1146 | h1146
                          · linarith only [h1064, h1065, h1146, hlam]
                          · rcases h0bigk with h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [hlam, p1148_0]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              rcases p1148_3 (m.d 0 1) (by simp) with h1150 | h1150
                              · rcases p1148_3 (m.d 0 2) (by simp) with h1151 | h1151
                                · linarith only [h0, h1151, hlam]
                                · rcases p1148_3 (m.d 0 3) (by simp) with h1153 | h1153
                                  · linarith only [h1, h1153, hlam]
                                  · linarith only [h1153, h4, hlam]
                              · linarith only [h0, h1150, hlam]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h1057, h1059, h1064, h1065, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1148_1]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h1059, h1064, h1065, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1148_1]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h1059, h1064, h1065, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1148_1]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h0, hlam, p1148_0]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [hlam, p1148_0]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h4, hlam, p1148_0]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h846, hlam, p1148_1]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h984, hlam, p1148_0]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h1, hlam, p1148_1]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h0, h4, hc12, hc23, hlam, hphi, p1148_1]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [hlam, p1148_0]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h1059, h1064, h1065, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1148_1, u3elo2]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h0, h4, h984, hc12, hlam, hphi, ht23, p1148_1, u3elo2]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h2, hlam, p1148_0]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h0, h846, hc12, hc24, hlam, hphi, p1148_1]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h1057, hlam, p1148_0]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [hlam, p1148_0]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h0, h1057, h4, h984, hc12, hlam, hphi, ht23, p1148_1, u3elo2]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h3, hlam, p1148_0]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h0, h1145, h984, hc12, hc24, hlam, hphi, p1148_1]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h1058, hlam, p1148_0]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [h1059, hlam, p1148_1]
                            · have p1148_0 := h1148c.1
                              have p1148_1 := h1148c.2.1
                              have p1148_2 := h1148c.2.2.1
                              have p1148_3 := h1148c.2.2.2
                              linarith only [hlam, p1148_0]
                        · linarith only [h1059, h1145, h846, hlam]
                      · linarith only [h1058, h1144, h4, hlam]
                    · linarith only [h1057, h1059, h1064, h1065, h1143, h4, hlam]
                · linarith only [h1057, h1064, h4, hc13, hlam, hphi, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1184 | h1184
            · linarith only [h0, h1184, h4, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1186 | h1186
              · linarith only [h1184, h1186, h984, hc02, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1188 | h1188
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1189 | h1189
                  · linarith only [h1059, h1189, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1191 | h1191
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1192 | h1192
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1193 | h1193
                        · linarith only [h0, h1059, h1191, h1193, h846, hc12, hlam, hphi, ht23, u3elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1195 | h1195
                          · linarith only [h0, h1193, h1195, h846, hc12, hlam, hphi, ht23, u3elo3]
                          · rcases h0bigk with h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [hlam, p1197_0]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              rcases p1197_3 (m.d 0 1) (by simp) with h1199 | h1199
                              · rcases p1197_3 (m.d 0 2) (by simp) with h1200 | h1200
                                · linarith only [h0, h1200, hlam]
                                · rcases p1197_3 (m.d 0 3) (by simp) with h1202 | h1202
                                  · linarith only [h1, h1202, hlam]
                                  · linarith only [h1202, h4, hlam]
                              · linarith only [h0, h1199, hlam]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [h1057, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1197_1]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              rcases p1197_3 (m.d 0 1) (by simp) with h1207 | h1207
                              · rcases p1197_3 (m.d 0 2) (by simp) with h1208 | h1208
                                · linarith only [h0, h1208, hlam]
                                · rcases p1197_3 (m.d 0 3) (by simp) with h1210 | h1210
                                  · linarith only [h1, h1210, hlam]
                                  · linarith only [h1057, h1210, hlam]
                              · linarith only [h1207, h2, hlam]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              rcases p1197_3 (m.d 0 1) (by simp) with h1214 | h1214
                              · rcases p1197_3 (m.d 0 2) (by simp) with h1215 | h1215
                                · linarith only [h0, h1215, hlam]
                                · rcases p1197_3 (m.d 0 3) (by simp) with h1217 | h1217
                                  · linarith only [h1, h1217, hlam]
                                  · linarith only [h1058, h1217, hlam]
                              · linarith only [h1214, h3, hlam]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [h0, hlam, p1197_0]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [hlam, p1197_0]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [h4, hlam, p1197_0]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [h846, hlam, p1197_1]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [h984, hlam, p1197_0]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [h1, hlam, p1197_1]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, p1197_1, u3elo0]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [hlam, p1197_0]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [h0, h4, h846, hc12, hlam, hphi, ht23, p1197_1, u3elo2]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1197_1, u3elo2]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [h2, hlam, p1197_0]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [h0, h846, hc12, hc24, hlam, hphi, p1197_1]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [h1057, hlam, p1197_0]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [hlam, p1197_0]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [h1059, hlam, p1197_0]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [h3, hlam, p1197_0]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [h0, h1192, h984, hc12, hlam, hphi, ht23, p1197_1, u3elo2]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [h1058, hlam, p1197_0]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [h1192, h984, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1197_1, u3elo2]
                            · have p1197_0 := h1197c.1
                              have p1197_1 := h1197c.2.1
                              have p1197_2 := h1197c.2.2.1
                              have p1197_3 := h1197c.2.2.2
                              linarith only [hlam, p1197_0]
                      · linarith only [h1058, h1192, h4, hlam]
                    · linarith only [h1, h1058, h1188, h1191, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h1057, h1188, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1244 | h1244
          · linarith only [h1057, h1058, h1244, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1246 | h1246
            · linarith only [h0, h1246, h4, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1248 | h1248
              · linarith only [h0, h1248, h984, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1250 | h1250
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1251 | h1251
                  · linarith only [h1244, h1251, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1253 | h1253
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1254 | h1254
                      · linarith only [h1, h1058, h1250, h1254, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · linarith only [h0, h1254, h4, hc12, hlam, hphi, ht23, u3elo4]
                    · linarith only [h0, h1253, h4, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h1057, h1058, h1250, hc13, hlam, hphi, u3elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1259 | h1259
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1260 | h1260
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1261 | h1261
            · linarith only [h0, h1261, h4, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1263 | h1263
              · linarith only [h1261, h1263, h984, hc02, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1265 | h1265
                · linarith only [h1, h1057, h1265, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1267 | h1267
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1268 | h1268
                    · linarith only [h1057, h1259, h1268, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h0, h1268, h4, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1057, h1260, h1265, h1267, hc13, hlam, hphi, u3elo3]
          · linarith only [h1057, h1259, h1260, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1273 | h1273
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1274 | h1274
            · linarith only [h0, h1274, h4, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1276 | h1276
              · linarith only [h0, h1276, h984, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1278 | h1278
                · linarith only [h1, h1057, h1278, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1280 | h1280
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1281 | h1281
                    · linarith only [h0, h1057, h1281, h4, hc12, hlam, hphi, ht23, u3elo2]
                    · linarith only [h0, h1281, h4, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1057, h1273, h1274, h1278, h1280, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1285 | h1285
            · linarith only [h0, h1285, h4, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1287 | h1287
              · linarith only [h0, h1273, h1287, h846, h984, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1289 | h1289
                · linarith only [h1, h1057, h1289, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1291 | h1291
                  · linarith only [h1273, h1291, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1293 | h1293
                    · linarith only [h0, h1057, h1293, h4, hc12, hlam, hphi, ht23, u3elo2]
                    · linarith only [h0, h1293, h4, hc12, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0_x0_x0 m hb0 hb3 hb4 h0 h1 h2 h3 h4
  · exact r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0_x0_x1 m hb0 hb3 hb4 h0 h1 h2 h3 h4

set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1296 | h1296
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1297 | h1297
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1298 | h1298
      · linarith only [h0, h1298, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1300 | h1300
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1301 | h1301
          · linarith only [h0, h1296, h1301, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1303 | h1303
            · linarith only [h1303, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1305 | h1305
              · linarith only [h0, h1301, h1305, h3, hc23, hlam, hphi, u3elo4]
              · linarith only [h0, h1296, h1301, h1305, h3, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1308 | h1308
          · linarith only [h1, h1300, h1308, h3, hc13, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1310 | h1310
            · linarith only [h0, h1297, h1310, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1312 | h1312
              · linarith only [h0, h1308, h1312, h3, hc23, hlam, hphi, u3elo4]
              · linarith only [h1296, h1298, h1312, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1315 | h1315
      · linarith only [h0, h1315, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1317 | h1317
        · linarith only [h1296, h1297, h1317, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1319 | h1319
          · linarith only [h1296, h1297, h1319, h2, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1321 | h1321
            · linarith only [h1321, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1323 | h1323
              · linarith only [h0, h1319, h1323, h3, hc23, hlam, hphi, u3elo4]
              · linarith only [h1296, h1297, h1321, h1323, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1326 | h1326
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1327 | h1327
      · linarith only [h0, h1296, h1327, h3, hc12, hlam, hphi, ht23, u3elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1329 | h1329
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1330 | h1330
          · linarith only [h1, h1330, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1332 | h1332
            · linarith only [h0, h1296, h1326, h1330, h1332, h3, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1334 | h1334
              · linarith only [h0, h1296, h1330, h1334, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1336 | h1336
                · linarith only [h1326, h1327, h1334, h1336, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1338 | h1338
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1339 | h1339
                    · linarith only [h1, h1332, h1338, h1339, h3, hlam]
                    · linarith only [h1, h1338, h1339, h3, hc34, hc45, hlam, hphi]
                  · linarith only [h1329, h1330, h1334, h1338, hc12, hlam, hphi, ht23, u3elo4]
        · linarith only [h1296, h1326, h1329, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1344 | h1344
      · linarith only [h0, h1344, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1346 | h1346
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1347 | h1347
          · linarith only [h1, h1347, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1349 | h1349
            · linarith only [h0, h1346, h1347, h1349, h3, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1351 | h1351
              · linarith only [h0, h1326, h1346, h1347, h1351, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1353 | h1353
                · linarith only [h0, h1296, h1344, h1353, h3, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1355 | h1355
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1356 | h1356
                    · linarith only [h1326, h1349, h1356, h2, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h1, h1355, h1356, h3, hc34, hc45, hlam, hphi]
                  · linarith only [h1346, h1347, h1351, h1355, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1360 | h1360
          · linarith only [h0, h1346, h1360, h3, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1362 | h1362
            · linarith only [h1362, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1364 | h1364
              · linarith only [h0, h1296, h1364, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1366 | h1366
                · linarith only [h0, h1344, h1366, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1368 | h1368
                  · linarith only [h1346, h1368, hc03, hlam, hphi, u3elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1370 | h1370
                    · linarith only [h1360, h1362, h1370, h2, h3, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1372 | h1372
                      · linarith only [h1296, h1346, h1372, hc02, hlam, hphi, ht23, u3elo2]
                      · linarith only [h0, h1296, h1372, hc12, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0_x0 m hb0 hb3 hb4 h0 h1 h2 h3
  · exact r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0_x1 m hb0 hb3 hb4 h0 h1 h2 h3

set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1375 | h1375
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1376 | h1376
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1377 | h1377
      · linarith only [h0, h1377, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1379 | h1379
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1380 | h1380
          · linarith only [h1, h1380, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1382 | h1382
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1383 | h1383
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1384 | h1384
                · linarith only [h0, h1380, h1384, h2, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h1376, h1380, h1384, h2, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h1, h1380, h1382, h1383, h2, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1388 | h1388
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1389 | h1389
                · linarith only [h0, h1380, h1389, h2, hc23, hlam, hphi, u3elo3]
                · linarith only [h1376, h1377, h1389, hc12, hc24, hlam, hphi]
              · linarith only [h0, h1379, h1388, h2, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1393 | h1393
          · linarith only [h1, h1393, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1395 | h1395
            · linarith only [h1376, h1379, h1393, h1395, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1397 | h1397
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1398 | h1398
                · linarith only [h0, h1393, h1398, h2, hc23, hlam, hphi, u3elo3]
                · linarith only [h1376, h1379, h1398, hc12, hc25, hlam, hphi]
              · linarith only [h1375, h1397, h2, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1402 | h1402
      · linarith only [h0, h1402, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1404 | h1404
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1405 | h1405
          · linarith only [h1, h1405, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1407 | h1407
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1408 | h1408
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1409 | h1409
                · linarith only [h0, h1376, h1405, h1409, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1411 | h1411
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1412 | h1412
                    · linarith only [h1376, h1405, h1412, hc02, hlam, hphi, ht23, u3elo1]
                    · linarith only [h1, h1409, h1411, h1412, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h1376, h1404, h1411, hc12, hlam, hphi, ht23, u3elo2]
              · linarith only [h0, h1376, h1404, h1405, h1408, h2, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h1376, h1404, h1407, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1418 | h1418
          · linarith only [h1, h1418, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1420 | h1420
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1421 | h1421
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1422 | h1422
                · linarith only [h0, h1404, h1418, h1420, h1422, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1424 | h1424
                  · linarith only [h0, h1404, h1424, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1426 | h1426
                    · linarith only [h1, h1404, h1418, h1420, h1426, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h1426, h2, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h1375, h1421, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1430 | h1430
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1431 | h1431
                · linarith only [h0, h1376, h1431, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1433 | h1433
                  · linarith only [h0, h1404, h1433, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1435 | h1435
                    · linarith only [h1, h1418, h1420, h1435, h2, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h1, h1431, h1435, h2, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h1375, h1430, h2, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1439 | h1439
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1440 | h1440
      · linarith only [h0, h1440, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1442 | h1442
        · linarith only [h0, h1375, h1442, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1444 | h1444
          · linarith only [h1, h1444, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1446 | h1446
            · linarith only [h1, h1375, h1444, h1446, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1448 | h1448
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1449 | h1449
                · linarith only [h0, h1375, h1444, h1448, h1449, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h1375, h1439, h1444, h1448, h1449, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1452 | h1452
                · linarith only [h0, h1446, h1448, h1452, h2, hc23, hlam, hphi, u3elo4]
                · linarith only [h0, h1439, h1446, h1448, h1452, h2, hc12, hlam, hphi, ht23, u3elo4]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1455 | h1455
      · linarith only [h0, h1455, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1457 | h1457
        · linarith only [h0, h1375, h1439, h1457, hc12, hlam, hphi, ht23, u3elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1459 | h1459
          · linarith only [h1, h1459, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1461 | h1461
            · linarith only [h0, h1375, h1459, h1461, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1463 | h1463
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1464 | h1464
                · linarith only [h0, h1439, h1459, h1464, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1466 | h1466
                  · linarith only [h1, h1375, h1457, h1464, h1466, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1468 | h1468
                    · linarith only [h1, h1375, h1459, h1463, h1468, hlam]
                    · linarith only [h1, h1464, h1468, h2, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1471 | h1471
                · linarith only [h0, h1439, h1471, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1473 | h1473
                  · linarith only [h0, h1457, h1473, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1475 | h1475
                    · linarith only [h1459, h1475, hc03, hlam, hphi, u3elo1]
                    · linarith only [h0, h1475, h2, hc12, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x0 m hb0 hb3 hb4 h0 h1 h2
  · exact r1l7_20_13_14_H_I_L_0_L_I_x0_x0_x1 m hb0 hb3 hb4 h0 h1 h2

set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

set_option maxHeartbeats 6332000 in
set_option maxHeartbeats 6332000 in
theorem r1l7_20_13_14_H_I_L_0_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_13_14_H_I_L_0_L_I_x0_x0 m hb0 hb3 hb4 h0 h1
  · exact r1l7_20_13_14_H_I_L_0_L_I_x0_x1 m hb0 hb3 hb4 h0 h1

end R2N4
