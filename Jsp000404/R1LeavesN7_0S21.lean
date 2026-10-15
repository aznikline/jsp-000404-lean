import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h10760 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 2 5 (by decide) (by decide) with h10761 | h10761
  · rcases m.htr 1 3 4 (by decide) (by decide) with h10762 | h10762
    · rcases m.htr 1 3 5 (by decide) (by decide) with h10763 | h10763
      · rcases m.htr 1 4 5 (by decide) (by decide) with h10764 | h10764
        · linarith only [h10764, h2, h9, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h10766 | h10766
          · rcases m.htr 2 3 5 (by decide) (by decide) with h10767 | h10767
            · rcases m.htr 2 4 5 (by decide) (by decide) with h10768 | h10768
              · linarith only [h10760, h10768, h2, h9, h9268, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h10770 | h10770
                · linarith only [h10760, h10766, h10770, h2, h9, hlam]
                · rcases h1bigk with h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c | h10772c
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [hlam, p10772_0]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    rcases p10772_3 (m.d 0 1) (by simp) with h10774 | h10774
                    · rcases p10772_3 (m.d 1 2) (by simp) with h10775 | h10775
                      · linarith only [h10775, hlam, p10772_0]
                      · rcases p10772_3 (m.d 1 3) (by simp) with h10777 | h10777
                        · linarith only [h1, h10777, hlam]
                        · linarith only [h10777, h9268, hlam]
                    · linarith only [h10774, hlam, p10772_0]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    rcases p10772_3 (m.d 0 1) (by simp) with h10781 | h10781
                    · rcases p10772_3 (m.d 1 2) (by simp) with h10782 | h10782
                      · linarith only [h0, h10782, hlam]
                      · rcases p10772_3 (m.d 1 3) (by simp) with h10784 | h10784
                        · linarith only [h10784, hlam, p10772_0]
                        · rcases p10772_3 (m.d 1 4) (by simp) with h10786 | h10786
                          · linarith only [h10786, h2, hlam]
                          · rcases p10772_3 (m.d 1 5) (by simp) with h10788 | h10788
                            · linarith only [h10788, h3, hlam]
                            · rcases h1emax with h10790 | h10790 | h10790 | h10790 | h10790
                              · linarith only [h0, h10790, h4, h9268, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases h2bigk with h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c | h10792c
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [hlam, p10792_0]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  rcases p10792_3 (m.d 0 2) (by simp) with h10794 | h10794
                                  · rcases p10792_3 (m.d 1 2) (by simp) with h10795 | h10795
                                    · linarith only [h0, h10795, hlam]
                                    · rcases p10792_3 (m.d 2 3) (by simp) with h10797 | h10797
                                      · linarith only [h10797, h4, hlam]
                                      · linarith only [h10797, h9268, hlam]
                                  · linarith only [h0, h10794, hlam]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [h0, h10761, h10766, h10768, h9268, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10792_1]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [h10761, h10768, h4, h9268, hlam, p10792_2]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [h10761, h4, h9268, hlam, p10792_2]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [h0, hlam, p10792_1]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [hlam, p10792_0]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [h9268, hlam, p10792_0]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [h10766, h4, h9268, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p10792_1]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [h0, h10766, h10768, h4, h9268, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10792_1]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [h4, hlam, p10792_0]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [h0, h10760, h10766, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10792_1]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [hlam, p10792_0]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  rcases p10792_3 (m.d 0 2) (by simp) with h10812 | h10812
                                  · rcases p10792_3 (m.d 1 2) (by simp) with h10813 | h10813
                                    · linarith only [h10813, h9268, hlam]
                                    · linarith only [h10760, h10813, hlam]
                                  · linarith only [h10812, h5, hlam]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  rcases p10792_3 (m.d 0 2) (by simp) with h10817 | h10817
                                  · rcases p10792_3 (m.d 1 2) (by simp) with h10818 | h10818
                                    · linarith only [h10818, h9268, hlam]
                                    · linarith only [h10761, h10818, hlam]
                                  · linarith only [h10817, h6, hlam]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [h5, hlam, p10792_0]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [h10760, hlam, p10792_0]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [h10766, hlam, p10792_0]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [hlam, p10792_0]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [h10768, hlam, p10792_0]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [h6, hlam, p10792_0]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [h10761, hlam, p10792_0]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [h10767, hlam, p10792_0]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [h0, h10761, h10766, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10792_1]
                                · have p10792_0 := h10792c.1
                                  have p10792_1 := h10792c.2.1
                                  have p10792_2 := h10792c.2.2.1
                                  have p10792_3 := h10792c.2.2.2
                                  linarith only [hlam, p10792_0]
                              · rcases h2bigk with h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [hlam, p10832_0]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  rcases p10832_3 (m.d 0 2) (by simp) with h10834 | h10834
                                  · rcases p10832_3 (m.d 1 2) (by simp) with h10835 | h10835
                                    · linarith only [h0, h10835, hlam]
                                    · rcases p10832_3 (m.d 2 3) (by simp) with h10837 | h10837
                                      · linarith only [h10837, h4, hlam]
                                      · linarith only [h10837, h9268, hlam]
                                  · linarith only [h0, h10834, hlam]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [h0, h10761, h9268, hc01, hc25, hlam, hphi, ht0b, ht5b, p10832_1]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [h10760, h4, h9268, hlam, p10832_2]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [h10761, h4, h9268, hlam, p10832_2]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [h0, hlam, p10832_1]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [hlam, p10832_0]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [h9268, hlam, p10832_0]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [h10766, h4, h9268, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p10832_1]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [h10790, h9268, hc25, hlam, hphi, ht01, ht0b, ht5b, p10832_1]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [h4, hlam, p10832_0]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [h0, h10760, h10766, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10832_1]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [hlam, p10832_0]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  rcases p10832_3 (m.d 0 2) (by simp) with h10852 | h10852
                                  · rcases p10832_3 (m.d 1 2) (by simp) with h10853 | h10853
                                    · linarith only [h10853, h9268, hlam]
                                    · linarith only [h10760, h10853, hlam]
                                  · linarith only [h10852, h5, hlam]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  rcases p10832_3 (m.d 0 2) (by simp) with h10857 | h10857
                                  · rcases p10832_3 (m.d 1 2) (by simp) with h10858 | h10858
                                    · linarith only [h10858, h9268, hlam]
                                    · linarith only [h10761, h10858, hlam]
                                  · linarith only [h10857, h6, hlam]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [h5, hlam, p10832_0]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [h10760, hlam, p10832_0]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [h10766, hlam, p10832_0]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [hlam, p10832_0]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [h10768, hlam, p10832_0]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [h6, hlam, p10832_0]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [h10761, hlam, p10832_0]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [h10767, hlam, p10832_0]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [h0, h10761, h10766, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10832_1]
                                · have p10832_0 := h10832c.1
                                  have p10832_1 := h10832c.2.1
                                  have p10832_2 := h10832c.2.2.1
                                  have p10832_3 := h10832c.2.2.2
                                  linarith only [hlam, p10832_0]
                              · rcases h2bigk with h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c | h10872c
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [hlam, p10872_0]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  rcases p10872_3 (m.d 0 2) (by simp) with h10874 | h10874
                                  · rcases p10872_3 (m.d 1 2) (by simp) with h10875 | h10875
                                    · linarith only [h0, h10875, hlam]
                                    · rcases p10872_3 (m.d 2 3) (by simp) with h10877 | h10877
                                      · linarith only [h10877, h4, hlam]
                                      · linarith only [h10877, h9268, hlam]
                                  · linarith only [h0, h10874, hlam]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [h0, h10760, h10766, h9268, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10872_1]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [h10760, h4, h9268, hlam, p10872_2]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [h10761, h4, h9268, hlam, p10872_2]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [h0, hlam, p10872_1]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [hlam, p10872_0]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [h9268, hlam, p10872_0]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [h10766, h4, h9268, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p10872_1]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [h4, h9268, hc02, hc25, hlam, hphi, ht0b, ht5b, p10872_1]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [h4, hlam, p10872_0]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [h0, h10760, h10766, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10872_1]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [hlam, p10872_0]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  rcases p10872_3 (m.d 0 2) (by simp) with h10892 | h10892
                                  · rcases p10872_3 (m.d 1 2) (by simp) with h10893 | h10893
                                    · linarith only [h10893, h9268, hlam]
                                    · linarith only [h10760, h10893, hlam]
                                  · linarith only [h10892, h5, hlam]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  rcases p10872_3 (m.d 0 2) (by simp) with h10897 | h10897
                                  · rcases p10872_3 (m.d 1 2) (by simp) with h10898 | h10898
                                    · linarith only [h10898, h9268, hlam]
                                    · linarith only [h10761, h10898, hlam]
                                  · linarith only [h10897, h6, hlam]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [h5, hlam, p10872_0]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [h10760, hlam, p10872_0]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [h10766, hlam, p10872_0]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [hlam, p10872_0]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [h10768, hlam, p10872_0]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [h6, hlam, p10872_0]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [h10761, hlam, p10872_0]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [h10767, hlam, p10872_0]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [h0, h10761, h10766, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10872_1]
                                · have p10872_0 := h10872c.1
                                  have p10872_1 := h10872c.2.1
                                  have p10872_2 := h10872c.2.2.1
                                  have p10872_3 := h10872c.2.2.2
                                  linarith only [hlam, p10872_0]
                              · rcases h2bigk with h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c | h10912c
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [hlam, p10912_0]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  rcases p10912_3 (m.d 0 2) (by simp) with h10914 | h10914
                                  · rcases p10912_3 (m.d 1 2) (by simp) with h10915 | h10915
                                    · linarith only [h0, h10915, hlam]
                                    · rcases p10912_3 (m.d 2 3) (by simp) with h10917 | h10917
                                      · linarith only [h10917, h4, hlam]
                                      · linarith only [h10917, h9268, hlam]
                                  · linarith only [h0, h10914, hlam]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [h0, h10760, h10766, h9268, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10912_1]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [h10760, h4, h9268, hlam, p10912_2]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [h10761, h4, h9268, hlam, p10912_2]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [h0, hlam, p10912_1]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [hlam, p10912_0]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [h9268, hlam, p10912_0]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [h10766, h4, h9268, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p10912_1]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [h4, h9268, hc02, hc25, hlam, hphi, ht0b, ht5b, p10912_1]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [h4, hlam, p10912_0]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [h0, h10760, h10766, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10912_1]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [hlam, p10912_0]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  rcases p10912_3 (m.d 0 2) (by simp) with h10932 | h10932
                                  · rcases p10912_3 (m.d 1 2) (by simp) with h10933 | h10933
                                    · linarith only [h10933, h9268, hlam]
                                    · linarith only [h10760, h10933, hlam]
                                  · linarith only [h10932, h5, hlam]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  rcases p10912_3 (m.d 0 2) (by simp) with h10937 | h10937
                                  · rcases p10912_3 (m.d 1 2) (by simp) with h10938 | h10938
                                    · linarith only [h10938, h9268, hlam]
                                    · linarith only [h10761, h10938, hlam]
                                  · linarith only [h10937, h6, hlam]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [h5, hlam, p10912_0]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [h10760, hlam, p10912_0]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [h10766, hlam, p10912_0]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [hlam, p10912_0]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [h10768, hlam, p10912_0]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [h6, hlam, p10912_0]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [h10761, hlam, p10912_0]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [h10767, hlam, p10912_0]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [h0, h10761, h10766, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10912_1]
                                · have p10912_0 := h10912c.1
                                  have p10912_1 := h10912c.2.1
                                  have p10912_2 := h10912c.2.2.1
                                  have p10912_3 := h10912c.2.2.2
                                  linarith only [hlam, p10912_0]
                    · linarith only [h10781, hlam, p10772_0]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    rcases p10772_3 (m.d 0 1) (by simp) with h10953 | h10953
                    · rcases p10772_3 (m.d 1 2) (by simp) with h10954 | h10954
                      · linarith only [h0, h10954, hlam]
                      · linarith only [h10760, h10954, hlam]
                    · linarith only [h10953, hlam, p10772_0]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    rcases p10772_3 (m.d 0 1) (by simp) with h10958 | h10958
                    · rcases p10772_3 (m.d 1 2) (by simp) with h10959 | h10959
                      · linarith only [h0, h10959, hlam]
                      · linarith only [h10761, h10959, hlam]
                    · linarith only [h10958, hlam, p10772_0]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [h0, hlam, p10772_0]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [hlam, p10772_0]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [h9268, hlam, p10772_1]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [h0, h4, h9268, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p10772_1]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [h0, h4, h9268, hc01, hc15, hlam, hphi, ht0b, ht5b, p10772_1]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [h1, hlam, p10772_0]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [h1, h10760, h10766, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10772_1]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [hlam, p10772_0]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    rcases p10772_3 (m.d 0 1) (by simp) with h10971 | h10971
                    · rcases p10772_3 (m.d 1 2) (by simp) with h10972 | h10972
                      · linarith only [h10972, h9268, hlam]
                      · linarith only [h10760, h10972, hlam]
                    · linarith only [h10971, h2, hlam]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    rcases p10772_3 (m.d 0 1) (by simp) with h10976 | h10976
                    · rcases p10772_3 (m.d 1 2) (by simp) with h10977 | h10977
                      · linarith only [h10977, h9268, hlam]
                      · linarith only [h10761, h10977, hlam]
                    · linarith only [h10976, h3, hlam]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [h2, hlam, p10772_0]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [h10760, hlam, p10772_0]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [h10762, hlam, p10772_1]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [hlam, p10772_0]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [h10764, hlam, p10772_1]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [h3, hlam, p10772_0]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [h10761, hlam, p10772_0]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [h10763, hlam, p10772_0]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [h0, h10760, h10761, h10766, h4, h9268, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10772_1]
                  · have p10772_0 := h10772c.1
                    have p10772_1 := h10772c.2.1
                    have p10772_2 := h10772c.2.2.1
                    have p10772_3 := h10772c.2.2.2
                    linarith only [hlam, p10772_0]
            · linarith only [h0, h10761, h10767, h4, h8, h9268, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h10760, h10766, h4, h7, h9268, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h10761, h10763, h9268, hlam]
    · linarith only [h10760, h10762, h7, h9, h9268, hc24, hc45, hlam, hphi]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h10995 | h10995
    · rcases m.htr 1 3 5 (by decide) (by decide) with h10996 | h10996
      · rcases m.htr 1 4 5 (by decide) (by decide) with h10997 | h10997
        · linarith only [h10997, h2, h9, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h10999 | h10999
          · rcases m.htr 2 3 5 (by decide) (by decide) with h11000 | h11000
            · rcases m.htr 2 4 5 (by decide) (by decide) with h11001 | h11001
              · linarith only [h10760, h10761, h11001, h6, h9, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h11003 | h11003
                · linarith only [h10760, h10761, h10999, h11003, h6, h9, hlam]
                · rcases h1bigk with h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c | h11005c
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [hlam, p11005_0]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    rcases p11005_3 (m.d 0 1) (by simp) with h11007 | h11007
                    · rcases p11005_3 (m.d 1 2) (by simp) with h11008 | h11008
                      · linarith only [h11008, hlam, p11005_0]
                      · rcases p11005_3 (m.d 1 3) (by simp) with h11010 | h11010
                        · linarith only [h1, h11010, hlam]
                        · linarith only [h11010, h9268, hlam]
                    · linarith only [h11007, hlam, p11005_0]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    rcases p11005_3 (m.d 0 1) (by simp) with h11014 | h11014
                    · rcases p11005_3 (m.d 1 2) (by simp) with h11015 | h11015
                      · linarith only [h0, h11015, hlam]
                      · rcases p11005_3 (m.d 1 3) (by simp) with h11017 | h11017
                        · linarith only [h11017, hlam, p11005_0]
                        · rcases p11005_3 (m.d 1 4) (by simp) with h11019 | h11019
                          · linarith only [h11019, h2, hlam]
                          · rcases p11005_3 (m.d 1 5) (by simp) with h11021 | h11021
                            · linarith only [h11021, h3, hlam]
                            · rcases h1emax with h11023 | h11023 | h11023 | h11023 | h11023
                              · linarith only [h0, h10760, h10999, h11023, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases h2bigk with h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c | h11025c
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [hlam, p11025_0]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  rcases p11025_3 (m.d 0 2) (by simp) with h11027 | h11027
                                  · rcases p11025_3 (m.d 1 2) (by simp) with h11028 | h11028
                                    · linarith only [h0, h11028, hlam]
                                    · rcases p11025_3 (m.d 2 3) (by simp) with h11030 | h11030
                                      · linarith only [h11030, h4, hlam]
                                      · linarith only [h11030, h9268, hlam]
                                  · linarith only [h0, h11027, hlam]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [h0, h10760, h10761, h10999, h11000, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11025_1]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [h10760, h10761, h11000, h4, hlam, p11025_2]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [h10760, h10761, h10999, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p11025_1]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [h0, hlam, p11025_1]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [hlam, p11025_0]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [h9268, hlam, p11025_0]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [h10761, h10999, h6, h9, hc34, hc45, hlam, hphi, p11025_1]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [h10761, hlam, p11025_0]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [h4, hlam, p11025_0]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [h0, h10760, h10999, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11025_1]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [hlam, p11025_0]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  rcases p11025_3 (m.d 0 2) (by simp) with h11045 | h11045
                                  · rcases p11025_3 (m.d 1 2) (by simp) with h11046 | h11046
                                    · linarith only [h11046, h9268, hlam]
                                    · linarith only [h10760, h11046, hlam]
                                  · linarith only [h11045, h5, hlam]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [h0, h10760, h10761, h10999, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11025_1]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [h5, hlam, p11025_0]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [h10760, hlam, p11025_0]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [h10999, hlam, p11025_0]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [hlam, p11025_0]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [h11001, hlam, p11025_0]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [h6, hlam, p11025_0]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [h0, h10760, h10999, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11025_1]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [h11000, hlam, p11025_0]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  rcases p11025_3 (m.d 0 2) (by simp) with h11059 | h11059
                                  · rcases p11025_3 (m.d 1 2) (by simp) with h11060 | h11060
                                    · linarith only [h10761, h11060, hlam]
                                    · linarith only [h10760, h11060, hlam]
                                  · linarith only [h11059, h5, hlam]
                                · have p11025_0 := h11025c.1
                                  have p11025_1 := h11025c.2.1
                                  have p11025_2 := h11025c.2.2.1
                                  have p11025_3 := h11025c.2.2.2
                                  linarith only [hlam, p11025_0]
                              · rcases h2bigk with h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c | h11065c
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [hlam, p11065_0]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  rcases p11065_3 (m.d 0 2) (by simp) with h11067 | h11067
                                  · rcases p11065_3 (m.d 1 2) (by simp) with h11068 | h11068
                                    · linarith only [h0, h11068, hlam]
                                    · rcases p11065_3 (m.d 2 3) (by simp) with h11070 | h11070
                                      · linarith only [h11070, h4, hlam]
                                      · linarith only [h11070, h9268, hlam]
                                  · linarith only [h0, h11067, hlam]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [h0, h10760, h10999, h9268, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11065_1]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [h10760, h4, h9268, hlam, p11065_2]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [h0, h10760, h10761, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p11065_1]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [h0, hlam, p11065_1]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [hlam, p11065_0]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [h9268, hlam, p11065_0]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [h0, h10761, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p11065_1]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [h10761, hlam, p11065_0]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [h4, hlam, p11065_0]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [h0, h10760, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p11065_1]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [hlam, p11065_0]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  rcases p11065_3 (m.d 0 2) (by simp) with h11085 | h11085
                                  · rcases p11065_3 (m.d 1 2) (by simp) with h11086 | h11086
                                    · linarith only [h11086, h9268, hlam]
                                    · linarith only [h10760, h11086, hlam]
                                  · linarith only [h11085, h5, hlam]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [h0, h10760, h10761, h10999, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11065_1]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [h5, hlam, p11065_0]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [h10760, hlam, p11065_0]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [h10999, hlam, p11065_0]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [hlam, p11065_0]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [h11001, hlam, p11065_0]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [h6, hlam, p11065_0]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [h0, h10760, h10999, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11065_1]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [h11000, hlam, p11065_0]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  rcases p11065_3 (m.d 0 2) (by simp) with h11099 | h11099
                                  · rcases p11065_3 (m.d 1 2) (by simp) with h11100 | h11100
                                    · linarith only [h10761, h11100, hlam]
                                    · linarith only [h10760, h11100, hlam]
                                  · linarith only [h11099, h5, hlam]
                                · have p11065_0 := h11065c.1
                                  have p11065_1 := h11065c.2.1
                                  have p11065_2 := h11065c.2.2.1
                                  have p11065_3 := h11065c.2.2.2
                                  linarith only [hlam, p11065_0]
                              · rcases h2bigk with h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c | h11105c
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [hlam, p11105_0]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  rcases p11105_3 (m.d 0 2) (by simp) with h11107 | h11107
                                  · rcases p11105_3 (m.d 1 2) (by simp) with h11108 | h11108
                                    · linarith only [h0, h11108, hlam]
                                    · rcases p11105_3 (m.d 2 3) (by simp) with h11110 | h11110
                                      · linarith only [h11110, h4, hlam]
                                      · linarith only [h11110, h9268, hlam]
                                  · linarith only [h0, h11107, hlam]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [h0, h10760, h10999, h9268, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11105_1]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [h10760, h4, h9268, hlam, p11105_2]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [h0, h10760, h10761, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p11105_1]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [h0, hlam, p11105_1]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [hlam, p11105_0]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [h9268, hlam, p11105_0]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [h9268, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p11005_1, p11105_1]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [h10761, hlam, p11105_0]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [h4, hlam, p11105_0]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [h0, h10760, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p11105_1]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [hlam, p11105_0]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  rcases p11105_3 (m.d 0 2) (by simp) with h11125 | h11125
                                  · rcases p11105_3 (m.d 1 2) (by simp) with h11126 | h11126
                                    · linarith only [h11126, h9268, hlam]
                                    · linarith only [h10760, h11126, hlam]
                                  · linarith only [h11125, h5, hlam]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [h0, h10760, h10761, h10999, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11105_1]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [h5, hlam, p11105_0]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [h10760, hlam, p11105_0]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [h10999, hlam, p11105_0]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [hlam, p11105_0]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [h11001, hlam, p11105_0]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [h6, hlam, p11105_0]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [h0, h10760, h10999, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11105_1]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [h11000, hlam, p11105_0]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  rcases p11105_3 (m.d 0 2) (by simp) with h11139 | h11139
                                  · rcases p11105_3 (m.d 1 2) (by simp) with h11140 | h11140
                                    · linarith only [h10761, h11140, hlam]
                                    · linarith only [h10760, h11140, hlam]
                                  · linarith only [h11139, h5, hlam]
                                · have p11105_0 := h11105c.1
                                  have p11105_1 := h11105c.2.1
                                  have p11105_2 := h11105c.2.2.1
                                  have p11105_3 := h11105c.2.2.2
                                  linarith only [hlam, p11105_0]
                              · rcases h2bigk with h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c | h11145c
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [hlam, p11145_0]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  rcases p11145_3 (m.d 0 2) (by simp) with h11147 | h11147
                                  · rcases p11145_3 (m.d 1 2) (by simp) with h11148 | h11148
                                    · linarith only [h0, h11148, hlam]
                                    · rcases p11145_3 (m.d 2 3) (by simp) with h11150 | h11150
                                      · linarith only [h11150, h4, hlam]
                                      · linarith only [h11150, h9268, hlam]
                                  · linarith only [h0, h11147, hlam]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [h0, h10760, h10999, h9268, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11145_1]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [h10760, h4, h9268, hlam, p11145_2]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [h0, h10760, h10761, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p11145_1]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [h0, hlam, p11145_1]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [hlam, p11145_0]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [h9268, hlam, p11145_0]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [h0, h10761, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p11145_1]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [h10761, hlam, p11145_0]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [h4, hlam, p11145_0]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [h0, h10760, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p11145_1]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [hlam, p11145_0]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  rcases p11145_3 (m.d 0 2) (by simp) with h11165 | h11165
                                  · rcases p11145_3 (m.d 1 2) (by simp) with h11166 | h11166
                                    · linarith only [h11166, h9268, hlam]
                                    · linarith only [h10760, h11166, hlam]
                                  · linarith only [h11165, h5, hlam]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [h0, h10761, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11145_1]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [h5, hlam, p11145_0]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [h10760, hlam, p11145_0]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [h10999, hlam, p11145_0]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [hlam, p11145_0]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [h11001, hlam, p11145_0]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [h6, hlam, p11145_0]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [h0, h10760, h10999, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11145_1]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [h11000, hlam, p11145_0]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  rcases p11145_3 (m.d 0 2) (by simp) with h11179 | h11179
                                  · rcases p11145_3 (m.d 1 2) (by simp) with h11180 | h11180
                                    · linarith only [h10761, h11180, hlam]
                                    · linarith only [h10760, h11180, hlam]
                                  · linarith only [h11179, h5, hlam]
                                · have p11145_0 := h11145c.1
                                  have p11145_1 := h11145c.2.1
                                  have p11145_2 := h11145c.2.2.1
                                  have p11145_3 := h11145c.2.2.2
                                  linarith only [hlam, p11145_0]
                    · linarith only [h11014, hlam, p11005_0]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    rcases p11005_3 (m.d 0 1) (by simp) with h11186 | h11186
                    · rcases p11005_3 (m.d 1 2) (by simp) with h11187 | h11187
                      · linarith only [h0, h11187, hlam]
                      · linarith only [h10760, h11187, hlam]
                    · linarith only [h11186, hlam, p11005_0]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    rcases p11005_3 (m.d 0 1) (by simp) with h11191 | h11191
                    · rcases p11005_3 (m.d 1 2) (by simp) with h11192 | h11192
                      · linarith only [h0, h11192, hlam]
                      · rcases p11005_3 (m.d 1 3) (by simp) with h11194 | h11194
                        · linarith only [h1, h11194, hlam]
                        · linarith only [h10996, h11194, hlam]
                    · linarith only [h11191, hlam, p11005_0]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [h0, hlam, p11005_0]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [hlam, p11005_0]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [h9268, hlam, p11005_1]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [h0, h4, h9268, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p11005_1]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [h10761, hlam, p11005_1]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [h1, hlam, p11005_0]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [h1, h10760, h10999, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11005_1]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [hlam, p11005_0]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    rcases p11005_3 (m.d 0 1) (by simp) with h11206 | h11206
                    · rcases p11005_3 (m.d 1 2) (by simp) with h11207 | h11207
                      · linarith only [h11207, h9268, hlam]
                      · linarith only [h10760, h11207, hlam]
                    · linarith only [h11206, h2, hlam]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [h0, h10760, h10761, h10999, h4, h9268, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11005_1]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [h2, hlam, p11005_0]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [h10760, hlam, p11005_0]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [h10995, hlam, p11005_1]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [hlam, p11005_0]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [h10997, hlam, p11005_1]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [h3, hlam, p11005_0]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [h10760, h10999, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11005_1]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [h10996, hlam, p11005_0]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    rcases p11005_3 (m.d 0 1) (by simp) with h11220 | h11220
                    · rcases p11005_3 (m.d 1 2) (by simp) with h11221 | h11221
                      · linarith only [h10761, h11221, hlam]
                      · linarith only [h10760, h11221, hlam]
                    · linarith only [h11220, h2, hlam]
                  · have p11005_0 := h11005c.1
                    have p11005_1 := h11005c.2.1
                    have p11005_2 := h11005c.2.2.1
                    have p11005_3 := h11005c.2.2.2
                    linarith only [hlam, p11005_0]
            · linarith only [h10996, h11000, h9268, hlam]
          · linarith only [h10999, h7, h9, h9268, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h11228 | h11228
        · linarith only [h11228, h2, h9, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h11230 | h11230
          · rcases m.htr 2 3 5 (by decide) (by decide) with h11231 | h11231
            · linarith only [h0, h10760, h10996, h11230, h11231, h4, h9268, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10760, h11230, h11231, h4, h8, h9268, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10760, h11230, h4, h7, h9268, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · linarith only [h10760, h10995, h7, h9, h9268, hc24, hc45, hlam, hphi]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h10760 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h11236 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 4 (by decide) (by decide) with h11237 | h11237
  · rcases m.htr 1 3 5 (by decide) (by decide) with h11238 | h11238
    · rcases m.htr 1 4 5 (by decide) (by decide) with h11239 | h11239
      · linarith only [h10760, h11236, h11239, h5, h9, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
      · linarith only [h10760, h11236, h11239, hlam]
    · linarith only [h10760, h11236, h11237, h11238, h5, h9, hc34, hc45, hlam, hphi]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h11243 | h11243
    · rcases m.htr 1 4 5 (by decide) (by decide) with h11244 | h11244
      · linarith only [h11236, h11237, h11244, h7, h9, h9268, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
      · linarith only [h10760, h11236, h11244, hlam]
    · linarith only [h11236, h11243, h9268, hlam]

end R2N4
