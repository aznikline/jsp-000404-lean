import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_8S12
import Jsp000404.R1LeavesN7_8S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1_x1 (m : N7Model)
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
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9893 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9894 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9895 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9896 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h9897 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h9898 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h10456 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h10458 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
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
  rcases m.htr 3 4 5 (by decide) (by decide) with h10733 | h10733
  · rcases h0bigk with h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c | h10734c
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [hlam, p10734_0]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [h0, hlam, p10734_1]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [h7600, hlam, p10734_0]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [h8836, hlam, p10734_1]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [h9666, hlam, p10734_1]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      rcases p10734_3 (m.d 0 1) (by simp) with h10740 | h10740
      · linarith only [h0, h10740, hlam]
      · rcases p10734_3 (m.d 0 2) (by simp) with h10742 | h10742
        · rcases p10734_3 (m.d 0 3) (by simp) with h10743 | h10743
          · linarith only [h10743, h9886, hlam]
          · linarith only [h10743, h7600, hlam]
        · linarith only [h0, h10742, hlam]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [hlam, p10734_0]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [h0, h10458, h10733, h9889, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10734_1]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [h0, h10458, h10733, h9889, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10734_1]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      rcases p10734_3 (m.d 0 1) (by simp) with h10750 | h10750
      · linarith only [h0, h10750, hlam]
      · rcases p10734_3 (m.d 0 2) (by simp) with h10752 | h10752
        · rcases p10734_3 (m.d 0 3) (by simp) with h10753 | h10753
          · linarith only [h10753, h9886, hlam]
          · linarith only [h10753, h9890, hlam]
        · linarith only [h10752, h9888, hlam]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      rcases p10734_3 (m.d 0 1) (by simp) with h10757 | h10757
      · linarith only [h10757, h7600, hlam]
      · rcases p10734_3 (m.d 0 2) (by simp) with h10759 | h10759
        · rcases p10734_3 (m.d 0 3) (by simp) with h10760 | h10760
          · rcases p10734_3 (m.d 0 4) (by simp) with h10761 | h10761
            · linarith only [h10761, h9889, hlam]
            · linarith only [h10761, h8836, hlam]
          · linarith only [h10760, h7600, hlam]
        · linarith only [h0, h10759, hlam]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [h9886, hlam, p10734_1]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [hlam, p10734_0]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [h10458, h10733, h9889, h9898, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10734_1]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      rcases p10734_3 (m.d 0 1) (by simp) with h10769 | h10769
      · linarith only [h10769, h7600, hlam]
      · rcases p10734_3 (m.d 0 2) (by simp) with h10771 | h10771
        · rcases p10734_3 (m.d 0 3) (by simp) with h10772 | h10772
          · rcases p10734_3 (m.d 0 4) (by simp) with h10773 | h10773
            · linarith only [h10773, h9889, hlam]
            · linarith only [h10773, h9891, hlam]
          · linarith only [h10772, h9890, hlam]
        · linarith only [h10771, h9888, hlam]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      rcases p10734_3 (m.d 0 1) (by simp) with h10778 | h10778
      · linarith only [h10778, h8836, hlam]
      · rcases p10734_3 (m.d 0 2) (by simp) with h10780 | h10780
        · rcases p10734_3 (m.d 0 3) (by simp) with h10781 | h10781
          · rcases p10734_3 (m.d 0 4) (by simp) with h10782 | h10782
            · rcases p10734_3 (m.d 0 5) (by simp) with h10783 | h10783
              · linarith only [h10783, h9891, hlam]
              · linarith only [h10783, h9666, hlam]
            · linarith only [h10782, h8836, hlam]
          · linarith only [h10781, h7600, hlam]
        · linarith only [h0, h10780, hlam]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [h9887, hlam, p10734_0]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [h9889, hlam, p10734_0]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [hlam, p10734_0]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      rcases p10734_3 (m.d 0 1) (by simp) with h10792 | h10792
      · linarith only [h10792, h8836, hlam]
      · rcases p10734_3 (m.d 0 2) (by simp) with h10794 | h10794
        · rcases p10734_3 (m.d 0 3) (by simp) with h10795 | h10795
          · rcases p10734_3 (m.d 0 4) (by simp) with h10796 | h10796
            · rcases p10734_3 (m.d 0 5) (by simp) with h10797 | h10797
              · linarith only [h10797, h9891, hlam]
              · rcases h2bigk with h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c | h10799c
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [hlam, p10799_0]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h0, hlam, p10799_1]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h10458, h10733, h9886, h9889, h9898, hlam, p10799_2]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h10458, h10733, h9886, h9889, hlam, p10799_2]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  rcases p10799_3 (m.d 0 2) (by simp) with h10804 | h10804
                  · rcases p10799_3 (m.d 1 2) (by simp) with h10805 | h10805
                    · rcases p10799_3 (m.d 2 3) (by simp) with h10806 | h10806
                      · linarith only [h10806, h9886, hlam]
                      · rcases p10799_3 (m.d 2 4) (by simp) with h10808 | h10808
                        · linarith only [h10808, h9887, hlam]
                        · rcases p10799_3 (m.d 2 5) (by simp) with h10810 | h10810
                          · linarith only [h10810, hlam, p10799_0]
                          · rcases h3bigk with h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c | h10812c
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [hlam, p10812_0]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [h7600, hlam, p10812_1]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [h10458, h10733, h9889, h9890, h9898, hlam, p10734_1, p10812_2]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [h10458, h10733, h9886, h9898, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10812_1]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              rcases p10812_3 (m.d 0 3) (by simp) with h10817 | h10817
                              · rcases p10812_3 (m.d 1 3) (by simp) with h10818 | h10818
                                · rcases p10812_3 (m.d 2 3) (by simp) with h10819 | h10819
                                  · linarith only [h10819, h9886, hlam]
                                  · rcases p10812_3 (m.d 3 4) (by simp) with h10821 | h10821
                                    · linarith only [h10821, h9889, hlam]
                                    · linarith only [h10733, h10821, hlam]
                                · linarith only [h10818, h9896, hlam]
                              · linarith only [h10817, hlam, p10812_0]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [h10458, h10733, h9889, h9892, h9898, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10812_1]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [hlam, p10812_0]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [h10458, h10733, h7600, h9889, h9890, h9898, hlam, p10734_1, p10812_2]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [h10458, h10733, h9898, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10812_1]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              rcases p10812_3 (m.d 0 3) (by simp) with h10830 | h10830
                              · linarith only [h10830, h7600, hlam]
                              · linarith only [h10830, h9890, hlam]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [h9886, hlam, p10812_0]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [h9892, hlam, p10812_0]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [hlam, p10812_0]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [h9898, hlam, p10812_0]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [h10456, hlam, p10812_0]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [h9889, hlam, p10812_0]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [h9895, hlam, p10812_0]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              rcases p10812_3 (m.d 0 3) (by simp) with h10840 | h10840
                              · rcases p10812_3 (m.d 1 3) (by simp) with h10841 | h10841
                                · rcases p10812_3 (m.d 2 3) (by simp) with h10842 | h10842
                                  · linarith only [h10842, hlam, p10812_0]
                                  · rcases p10812_3 (m.d 3 4) (by simp) with h10844 | h10844
                                    · rcases p10812_3 (m.d 3 5) (by simp) with h10845 | h10845
                                      · linarith only [h10733, h10845, hlam]
                                      · linarith only [h10456, h10845, hlam]
                                    · linarith only [h10844, hlam, p10812_0]
                                · linarith only [h10841, h9892, hlam]
                              · linarith only [h10840, h9886, hlam]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [hlam, p10812_0]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [h10458, h10733, h9898, hc23, hc34, hlam, hphi, p10812_1]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [h9890, hlam, p10812_0]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [h9896, hlam, p10812_0]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [h9889, h9890, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10734_1, p10812_1]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [h10733, hlam, p10812_0]
                            · have p10812_0 := h10812c.1
                              have p10812_1 := h10812c.2.1
                              have p10812_2 := h10812c.2.2.1
                              have p10812_3 := h10812c.2.2.2
                              linarith only [hlam, p10812_0]
                    · linarith only [h10805, h9894, hlam]
                  · linarith only [h10804, hlam, p10799_0]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h9886, h9889, hc12, hlam, hphi, ht01, ht0b, ht5b, p10734_1, p10799_1, u5ehi0]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [hlam, p10799_0]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h0, h10458, h9886, h9889, h9891, h9898, hlam, p10734_1, p10799_2]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h0, h10458, h9886, h9889, h9891, hlam, p10734_1, p10799_2]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  rcases p10799_3 (m.d 0 2) (by simp) with h10864 | h10864
                  · linarith only [h0, h10864, hlam]
                  · linarith only [h10864, h9888, hlam]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h9886, hlam, p10799_0]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h9892, hlam, p10799_0]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [hlam, p10799_0]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h9898, hlam, p10799_0]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h10456, hlam, p10799_0]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h9887, hlam, p10799_0]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h9893, hlam, p10799_0]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h0, h10458, h10733, h9886, h9889, h9890, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10734_1, p10799_1]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [hlam, p10799_0]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h10458, hlam, p10799_1]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h9888, hlam, p10799_0]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h9894, hlam, p10799_0]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h0, h9886, h9888, h9889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10734_1, p10799_1]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [h0, h10458, h10733, h9886, h9889, h9890, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10734_1, p10799_1]
                · have p10799_0 := h10799c.1
                  have p10799_1 := h10799c.2.1
                  have p10799_2 := h10799c.2.2.1
                  have p10799_3 := h10799c.2.2.2
                  linarith only [hlam, p10799_0]
            · linarith only [h10796, h9891, hlam]
          · linarith only [h10795, h9890, hlam]
        · linarith only [h10794, h9888, hlam]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      rcases p10734_3 (m.d 0 1) (by simp) with h10885 | h10885
      · linarith only [h10885, h9666, hlam]
      · rcases p10734_3 (m.d 0 2) (by simp) with h10887 | h10887
        · rcases p10734_3 (m.d 0 3) (by simp) with h10888 | h10888
          · rcases p10734_3 (m.d 0 4) (by simp) with h10889 | h10889
            · rcases p10734_3 (m.d 0 5) (by simp) with h10890 | h10890
              · rcases h2bigk with h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c | h10891c
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [hlam, p10891_0]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h0, hlam, p10891_1]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h10458, h10733, h9886, h9889, h9898, hlam, p10891_2]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h10458, h10733, h9886, h9889, hlam, p10891_2]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  rcases p10891_3 (m.d 0 2) (by simp) with h10896 | h10896
                  · rcases p10891_3 (m.d 1 2) (by simp) with h10897 | h10897
                    · rcases p10891_3 (m.d 2 3) (by simp) with h10898 | h10898
                      · linarith only [h10898, h9886, hlam]
                      · rcases p10891_3 (m.d 2 4) (by simp) with h10900 | h10900
                        · linarith only [h10900, h9887, hlam]
                        · rcases p10891_3 (m.d 2 5) (by simp) with h10902 | h10902
                          · linarith only [h10902, hlam, p10891_0]
                          · rcases h3bigk with h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c | h10904c
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [hlam, p10904_0]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [h7600, hlam, p10904_1]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [h10458, h10733, h9889, h9898, hlam, p10904_2]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [h0, h10458, h10733, h9886, h9898, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10904_1]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              rcases p10904_3 (m.d 0 3) (by simp) with h10909 | h10909
                              · rcases p10904_3 (m.d 1 3) (by simp) with h10910 | h10910
                                · rcases p10904_3 (m.d 2 3) (by simp) with h10911 | h10911
                                  · linarith only [h10911, h9886, hlam]
                                  · rcases p10904_3 (m.d 3 4) (by simp) with h10913 | h10913
                                    · linarith only [h10913, h9889, hlam]
                                    · linarith only [h10733, h10913, hlam]
                                · linarith only [h10910, h9896, hlam]
                              · linarith only [h10909, hlam, p10904_0]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [h10458, h10733, h9889, h9892, h9898, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10904_1]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [hlam, p10904_0]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [h10458, h10733, h7600, h9889, h9898, hlam, p10904_2]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [h10458, h10733, h9898, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10904_1]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              rcases p10904_3 (m.d 0 3) (by simp) with h10922 | h10922
                              · linarith only [h10922, h7600, hlam]
                              · linarith only [h10922, h9890, hlam]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [h9886, hlam, p10904_0]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [h9892, hlam, p10904_0]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [hlam, p10904_0]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [h9898, hlam, p10904_0]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [h10456, hlam, p10904_0]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [h9889, hlam, p10904_0]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [h9895, hlam, p10904_0]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              rcases p10904_3 (m.d 0 3) (by simp) with h10932 | h10932
                              · rcases p10904_3 (m.d 1 3) (by simp) with h10933 | h10933
                                · rcases p10904_3 (m.d 2 3) (by simp) with h10934 | h10934
                                  · linarith only [h10934, hlam, p10904_0]
                                  · rcases p10904_3 (m.d 3 4) (by simp) with h10936 | h10936
                                    · rcases p10904_3 (m.d 3 5) (by simp) with h10937 | h10937
                                      · linarith only [h10733, h10937, hlam]
                                      · linarith only [h10456, h10937, hlam]
                                    · linarith only [h10936, hlam, p10904_0]
                                · linarith only [h10933, h9892, hlam]
                              · linarith only [h10932, h9886, hlam]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [hlam, p10904_0]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [h10458, h10733, h9889, h9898, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10904_1]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [h9890, hlam, p10904_0]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [h9896, hlam, p10904_0]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              rcases p10904_3 (m.d 0 3) (by simp) with h10947 | h10947
                              · rcases p10904_3 (m.d 1 3) (by simp) with h10948 | h10948
                                · rcases p10904_3 (m.d 2 3) (by simp) with h10949 | h10949
                                  · linarith only [h10949, hlam, p10904_0]
                                  · rcases p10904_3 (m.d 3 4) (by simp) with h10951 | h10951
                                    · rcases p10904_3 (m.d 3 5) (by simp) with h10952 | h10952
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
                                          linarith only [h9666, hlam, p10953_1]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          rcases p10953_3 (m.d 0 5) (by simp) with h10956 | h10956
                                          · rcases p10953_3 (m.d 1 5) (by simp) with h10957 | h10957
                                            · rcases p10953_3 (m.d 2 5) (by simp) with h10958 | h10958
                                              · linarith only [h10958, h9888, hlam]
                                              · rcases p10953_3 (m.d 3 5) (by simp) with h10960 | h10960
                                                · linarith only [h10960, h9890, hlam]
                                                · linarith only [h10456, h10960, hlam]
                                            · linarith only [h10957, h9894, hlam]
                                          · linarith only [h10956, h9888, hlam]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10904_1, p10953_1]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          rcases p10953_3 (m.d 0 5) (by simp) with h10966 | h10966
                                          · rcases p10953_3 (m.d 1 5) (by simp) with h10967 | h10967
                                            · rcases p10953_3 (m.d 2 5) (by simp) with h10968 | h10968
                                              · linarith only [h10968, h9888, hlam]
                                              · rcases p10953_3 (m.d 3 5) (by simp) with h10970 | h10970
                                                · linarith only [h10970, h9890, hlam]
                                                · linarith only [h10733, h10970, hlam]
                                            · linarith only [h10967, h9897, hlam]
                                          · linarith only [h10966, h9891, hlam]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [h9892, h9895, h9897, hc01, hc12, hlam, hphi, p10734_1, p10953_1]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [hlam, p10953_0]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          rcases p10953_3 (m.d 0 5) (by simp) with h10977 | h10977
                                          · linarith only [h10977, h9666, hlam]
                                          · linarith only [h10977, h9888, hlam]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [h9892, h9895, h9897, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10904_1, p10953_1]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          rcases p10953_3 (m.d 0 5) (by simp) with h10981 | h10981
                                          · linarith only [h10981, h9666, hlam]
                                          · linarith only [h10981, h9891, hlam]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [h9888, hlam, p10953_1]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [h9894, hlam, p10953_1]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [hlam, p10953_0]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [h10456, hlam, p10953_1]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [h10458, hlam, p10953_1]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [h9890, hlam, p10953_0]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [h9896, hlam, p10953_0]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [h7600, h9890, h9892, hc12, hlam, hphi, ht01, ht0b, ht5b, p10953_1, u5ehi2]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [hlam, p10953_0]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [h10458, h10733, h7600, h9889, h9892, h9898, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10953_1]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [h9891, hlam, p10953_0]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [h9897, hlam, p10953_0]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [h7600, h9889, h9891, h9892, hc12, hlam, hphi, ht01, ht0b, ht5b, p10953_1, u5ehi2]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [h10733, hlam, p10953_0]
                                        · have p10953_0 := h10953c.1
                                          have p10953_1 := h10953c.2.1
                                          have p10953_2 := h10953c.2.2.1
                                          have p10953_3 := h10953c.2.2.2
                                          linarith only [hlam, p10953_0]
                                      · linarith only [h10952, hlam, p10904_0]
                                    · linarith only [h10951, h9898, hlam]
                                · linarith only [h10948, h9892, hlam]
                              · linarith only [h10947, h9886, hlam]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [h10733, hlam, p10904_0]
                            · have p10904_0 := h10904c.1
                              have p10904_1 := h10904c.2.1
                              have p10904_2 := h10904c.2.2.1
                              have p10904_3 := h10904c.2.2.2
                              linarith only [hlam, p10904_0]
                    · linarith only [h10897, h9894, hlam]
                  · linarith only [h10896, hlam, p10891_0]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h10733, h9886, h9889, hc12, hlam, hphi, ht01, ht0b, ht5b, p10891_1, u5ehi3]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [hlam, p10891_0]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h0, h10458, h10733, h9886, h9889, h9898, hlam, p10891_2]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h0, h10458, h10733, h9886, h9889, hlam, p10891_2]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  rcases p10891_3 (m.d 0 2) (by simp) with h11011 | h11011
                  · linarith only [h0, h11011, hlam]
                  · linarith only [h11011, h9888, hlam]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h9886, hlam, p10891_0]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h9892, hlam, p10891_0]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [hlam, p10891_0]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h9898, hlam, p10891_0]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h10456, hlam, p10891_0]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h9887, hlam, p10891_0]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h9893, hlam, p10891_0]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h0, h10458, h10733, h9886, h9889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10891_1]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [hlam, p10891_0]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h10458, hlam, p10891_1]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h9888, hlam, p10891_0]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h9894, hlam, p10891_0]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h0, h10458, h10733, h9886, h9889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10891_1]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [h0, h10458, h10733, h9886, h9889, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10891_1]
                · have p10891_0 := h10891c.1
                  have p10891_1 := h10891c.2.1
                  have p10891_2 := h10891c.2.2.1
                  have p10891_3 := h10891c.2.2.2
                  linarith only [hlam, p10891_0]
              · linarith only [h10890, h9666, hlam]
            · linarith only [h10889, h8836, hlam]
          · linarith only [h10888, h7600, hlam]
        · linarith only [h0, h10887, hlam]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [h9888, hlam, p10734_1]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [h9890, hlam, p10734_0]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [h9891, hlam, p10734_1]
    · have p10734_0 := h10734c.1
      have p10734_1 := h10734c.2.1
      have p10734_2 := h10734c.2.2.1
      have p10734_3 := h10734c.2.2.2
      linarith only [hlam, p10734_0]
  · rcases h0bigk with h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c | h11037c
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [hlam, p11037_0]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [h0, hlam, p11037_1]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [h7600, hlam, p11037_0]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [h8836, hlam, p11037_1]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [h9666, hlam, p11037_1]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      rcases p11037_3 (m.d 0 1) (by simp) with h11043 | h11043
      · linarith only [h0, h11043, hlam]
      · rcases p11037_3 (m.d 0 2) (by simp) with h11045 | h11045
        · rcases p11037_3 (m.d 0 3) (by simp) with h11046 | h11046
          · linarith only [h11046, h9886, hlam]
          · linarith only [h11046, h7600, hlam]
        · linarith only [h0, h11045, hlam]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [hlam, p11037_0]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [h0, h10456, h10733, h9889, h9891, hc12, hlam, hphi, ht01, ht0b, ht5b, p11037_1, u5ehi2]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [h0, h10456, h10733, h9891, hc12, hlam, hphi, ht01, ht0b, ht5b, p11037_1, u5ehi2]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [h0, h10733, h9891, h9898, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11037_1]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      rcases p11037_3 (m.d 0 1) (by simp) with h11054 | h11054
      · linarith only [h11054, h7600, hlam]
      · rcases p11037_3 (m.d 0 2) (by simp) with h11056 | h11056
        · rcases p11037_3 (m.d 0 3) (by simp) with h11057 | h11057
          · rcases p11037_3 (m.d 0 4) (by simp) with h11058 | h11058
            · linarith only [h11058, h9889, hlam]
            · linarith only [h11058, h8836, hlam]
          · linarith only [h11057, h7600, hlam]
        · linarith only [h0, h11056, hlam]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [h9886, hlam, p11037_1]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [hlam, p11037_0]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [h10733, h9891, h9898, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11037_1]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [h10733, h7600, h9891, h9892, h9898, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11037_1]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      rcases p11037_3 (m.d 0 1) (by simp) with h11067 | h11067
      · linarith only [h11067, h8836, hlam]
      · rcases p11037_3 (m.d 0 2) (by simp) with h11069 | h11069
        · rcases p11037_3 (m.d 0 3) (by simp) with h11070 | h11070
          · rcases p11037_3 (m.d 0 4) (by simp) with h11071 | h11071
            · rcases p11037_3 (m.d 0 5) (by simp) with h11072 | h11072
              · linarith only [h11072, h9891, hlam]
              · linarith only [h11072, h9666, hlam]
            · linarith only [h11071, h8836, hlam]
          · linarith only [h11070, h7600, hlam]
        · linarith only [h0, h11069, hlam]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [h9887, hlam, p11037_0]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [h9889, hlam, p11037_0]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [hlam, p11037_0]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [h10733, h9891, h9898, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11037_1]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      rcases p11037_3 (m.d 0 1) (by simp) with h11082 | h11082
      · linarith only [h11082, h9666, hlam]
      · rcases p11037_3 (m.d 0 2) (by simp) with h11084 | h11084
        · rcases p11037_3 (m.d 0 3) (by simp) with h11085 | h11085
          · rcases p11037_3 (m.d 0 4) (by simp) with h11086 | h11086
            · rcases p11037_3 (m.d 0 5) (by simp) with h11087 | h11087
              · rcases h2bigk with h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [hlam, p11088_0]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [h0, hlam, p11088_1]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [h10733, h9886, h9889, h9891, h9898, hlam, p11088_2]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  rcases p11088_3 (m.d 0 2) (by simp) with h11092 | h11092
                  · rcases p11088_3 (m.d 1 2) (by simp) with h11093 | h11093
                    · rcases p11088_3 (m.d 2 3) (by simp) with h11094 | h11094
                      · linarith only [h11094, h9886, hlam]
                      · rcases p11088_3 (m.d 2 4) (by simp) with h11096 | h11096
                        · linarith only [h11096, hlam, p11088_0]
                        · rcases p11088_3 (m.d 2 5) (by simp) with h11098 | h11098
                          · linarith only [h11098, h9888, hlam]
                          · linarith only [h10458, h11098, hlam]
                    · linarith only [h11093, h9893, hlam]
                  · linarith only [h11092, hlam, p11088_0]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  rcases p11088_3 (m.d 0 2) (by simp) with h11103 | h11103
                  · rcases p11088_3 (m.d 1 2) (by simp) with h11104 | h11104
                    · rcases p11088_3 (m.d 2 3) (by simp) with h11105 | h11105
                      · linarith only [h11105, h9886, hlam]
                      · rcases p11088_3 (m.d 2 4) (by simp) with h11107 | h11107
                        · linarith only [h11107, h9887, hlam]
                        · rcases p11088_3 (m.d 2 5) (by simp) with h11109 | h11109
                          · linarith only [h11109, hlam, p11088_0]
                          · rcases h3bigk with h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c | h11111c
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [hlam, p11111_0]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [h7600, hlam, p11111_1]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [h10733, h9889, h9891, h9898, hlam, p11111_2]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              rcases p11111_3 (m.d 0 3) (by simp) with h11115 | h11115
                              · rcases p11111_3 (m.d 1 3) (by simp) with h11116 | h11116
                                · rcases p11111_3 (m.d 2 3) (by simp) with h11117 | h11117
                                  · linarith only [h11117, h9886, hlam]
                                  · rcases p11111_3 (m.d 3 4) (by simp) with h11119 | h11119
                                    · linarith only [h11119, hlam, p11111_0]
                                    · rcases p11111_3 (m.d 3 5) (by simp) with h11121 | h11121
                                      · linarith only [h11121, h9890, hlam]
                                      · linarith only [h10733, h11121, hlam]
                                · linarith only [h11116, h9895, hlam]
                              · linarith only [h11115, hlam, p11111_0]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              rcases p11111_3 (m.d 0 3) (by simp) with h11126 | h11126
                              · rcases p11111_3 (m.d 1 3) (by simp) with h11127 | h11127
                                · rcases p11111_3 (m.d 2 3) (by simp) with h11128 | h11128
                                  · linarith only [h11128, h9886, hlam]
                                  · rcases p11111_3 (m.d 3 4) (by simp) with h11130 | h11130
                                    · linarith only [h11130, h9889, hlam]
                                    · rcases p11111_3 (m.d 3 5) (by simp) with h11132 | h11132
                                      · linarith only [h11132, hlam, p11111_0]
                                      · rcases h5bigk with h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c | h11134c
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [hlam, p11134_0]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [h9666, hlam, p11134_1]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          rcases p11134_3 (m.d 0 5) (by simp) with h11137 | h11137
                                          · rcases p11134_3 (m.d 1 5) (by simp) with h11138 | h11138
                                            · rcases p11134_3 (m.d 2 5) (by simp) with h11139 | h11139
                                              · linarith only [h11139, h9888, hlam]
                                              · rcases p11134_3 (m.d 3 5) (by simp) with h11141 | h11141
                                                · linarith only [h11141, h9890, hlam]
                                                · linarith only [h10456, h11141, hlam]
                                            · linarith only [h11138, h9894, hlam]
                                          · linarith only [h11137, h9888, hlam]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          rcases p11134_3 (m.d 0 5) (by simp) with h11146 | h11146
                                          · rcases p11134_3 (m.d 1 5) (by simp) with h11147 | h11147
                                            · rcases p11134_3 (m.d 2 5) (by simp) with h11148 | h11148
                                              · linarith only [h11148, h9888, hlam]
                                              · rcases p11134_3 (m.d 3 5) (by simp) with h11150 | h11150
                                                · linarith only [h11150, h9890, hlam]
                                                · rcases p11134_3 (m.d 4 5) (by simp) with h11152 | h11152
                                                  · linarith only [h11152, h9891, hlam]
                                                  · linarith only [h10733, h11152, hlam]
                                            · linarith only [h11147, h9896, hlam]
                                          · linarith only [h11146, h9890, hlam]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [h10733, h9886, h9889, h9891, h9898, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11134_1]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [h9892, h9895, h9897, hc01, hc12, hlam, hphi, p11037_1, p11134_1]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [hlam, p11134_0]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          rcases p11134_3 (m.d 0 5) (by simp) with h11160 | h11160
                                          · linarith only [h11160, h9666, hlam]
                                          · linarith only [h11160, h9888, hlam]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          rcases p11134_3 (m.d 0 5) (by simp) with h11163 | h11163
                                          · linarith only [h11163, h9666, hlam]
                                          · linarith only [h11163, h9890, hlam]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [h10733, h9892, h9895, h9897, h9898, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11134_1]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [h9888, hlam, p11134_1]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [h9894, hlam, p11134_1]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [hlam, p11134_0]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [h10456, hlam, p11134_1]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [h10458, hlam, p11134_1]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [h9890, hlam, p11134_0]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [h9896, hlam, p11134_0]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [h0, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, p11111_1, p11134_1, u5ehi2]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [hlam, p11134_0]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [h10733, hlam, p11134_1]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [h9891, hlam, p11134_0]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [h9897, hlam, p11134_0]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [h0, h9886, h9889, h9891, hc12, hlam, hphi, ht01, ht0b, ht5b, p11134_1, u5ehi2]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [h0, h9886, h9889, h9891, hc12, hlam, hphi, ht01, ht0b, ht5b, p11134_1, u5ehi3]
                                        · have p11134_0 := h11134c.1
                                          have p11134_1 := h11134c.2.1
                                          have p11134_2 := h11134c.2.2.1
                                          have p11134_3 := h11134c.2.2.2
                                          linarith only [hlam, p11134_0]
                                · linarith only [h11127, h9896, hlam]
                              · linarith only [h11126, hlam, p11111_0]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [h9889, h9891, h9892, hc12, hlam, hphi, ht01, ht0b, ht5b, p11111_1, u5ehi4]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [hlam, p11111_0]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [h10733, h7600, h9889, h9891, h9898, hlam, p11111_2]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              rcases p11111_3 (m.d 0 3) (by simp) with h11187 | h11187
                              · linarith only [h11187, h7600, hlam]
                              · linarith only [h11187, h9889, hlam]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              rcases p11111_3 (m.d 0 3) (by simp) with h11190 | h11190
                              · linarith only [h11190, h7600, hlam]
                              · linarith only [h11190, h9890, hlam]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [h9886, hlam, p11111_0]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [h9892, hlam, p11111_0]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [hlam, p11111_0]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [h9898, hlam, p11111_0]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [h10456, hlam, p11111_0]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [h9889, hlam, p11111_0]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [h9895, hlam, p11111_0]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [h10733, h7600, h9889, h9891, h9892, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11111_1]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [hlam, p11111_0]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [h10733, hlam, p11111_1]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [h9890, hlam, p11111_0]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [h9896, hlam, p11111_0]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              rcases p11111_3 (m.d 0 3) (by simp) with h11205 | h11205
                              · rcases p11111_3 (m.d 1 3) (by simp) with h11206 | h11206
                                · rcases p11111_3 (m.d 2 3) (by simp) with h11207 | h11207
                                  · linarith only [h11207, hlam, p11111_0]
                                  · rcases p11111_3 (m.d 3 4) (by simp) with h11209 | h11209
                                    · linarith only [h10733, h11209, hlam]
                                    · linarith only [h11209, h9898, hlam]
                                · linarith only [h11206, h9892, hlam]
                              · linarith only [h11205, h9886, hlam]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [h7600, h9890, h9892, h9898, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11111_1]
                            · have p11111_0 := h11111c.1
                              have p11111_1 := h11111c.2.1
                              have p11111_2 := h11111c.2.2.1
                              have p11111_3 := h11111c.2.2.2
                              linarith only [hlam, p11111_0]
                    · linarith only [h11104, h9894, hlam]
                  · linarith only [h11103, hlam, p11088_0]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [h9886, h9890, hc12, hlam, hphi, ht01, ht0b, ht5b, p11088_1, u5ehi3]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [hlam, p11088_0]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [h0, h10733, h9886, h9889, h9891, h9898, hlam, p11088_2]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  rcases p11088_3 (m.d 0 2) (by simp) with h11221 | h11221
                  · linarith only [h0, h11221, hlam]
                  · linarith only [h11221, h9887, hlam]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  rcases p11088_3 (m.d 0 2) (by simp) with h11224 | h11224
                  · linarith only [h0, h11224, hlam]
                  · linarith only [h11224, h9888, hlam]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [h9886, hlam, p11088_0]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [h9892, hlam, p11088_0]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [hlam, p11088_0]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [h9898, hlam, p11088_0]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [h10456, hlam, p11088_0]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [h9887, hlam, p11088_0]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [h9893, hlam, p11088_0]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [h0, h10733, h9886, h9889, h9891, h9898, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11088_1]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [hlam, p11088_0]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [h10458, hlam, p11088_1]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [h9888, hlam, p11088_0]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [h9894, hlam, p11088_0]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  rcases p11088_3 (m.d 0 2) (by simp) with h11239 | h11239
                  · rcases p11088_3 (m.d 1 2) (by simp) with h11240 | h11240
                    · rcases p11088_3 (m.d 2 3) (by simp) with h11241 | h11241
                      · linarith only [h10456, h11241, hlam]
                      · rcases p11088_3 (m.d 2 4) (by simp) with h11243 | h11243
                        · linarith only [h10458, h11243, hlam]
                        · linarith only [h11243, h9898, hlam]
                    · linarith only [h11240, h9892, hlam]
                  · linarith only [h11239, h9886, hlam]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  rcases p11088_3 (m.d 0 2) (by simp) with h11248 | h11248
                  · rcases p11088_3 (m.d 1 2) (by simp) with h11249 | h11249
                    · rcases p11088_3 (m.d 2 3) (by simp) with h11250 | h11250
                      · linarith only [h10456, h11250, hlam]
                      · rcases p11088_3 (m.d 2 4) (by simp) with h11252 | h11252
                        · linarith only [h10458, h11252, hlam]
                        · rcases p11088_3 (m.d 2 5) (by simp) with h11254 | h11254
                          · rcases h3bigk with h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c | h11255c
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [hlam, p11255_0]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [h7600, hlam, p11255_1]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [h10456, h9890, h9898, hlam, p11088_1, p11255_2]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              rcases p11255_3 (m.d 0 3) (by simp) with h11259 | h11259
                              · rcases p11255_3 (m.d 1 3) (by simp) with h11260 | h11260
                                · rcases p11255_3 (m.d 2 3) (by simp) with h11261 | h11261
                                  · linarith only [h11261, h9886, hlam]
                                  · rcases p11255_3 (m.d 3 4) (by simp) with h11263 | h11263
                                    · linarith only [h11263, hlam, p11255_0]
                                    · rcases p11255_3 (m.d 3 5) (by simp) with h11265 | h11265
                                      · linarith only [h11265, h9890, hlam]
                                      · linarith only [h10733, h11265, hlam]
                                · linarith only [h11260, h9895, hlam]
                              · linarith only [h11259, hlam, p11255_0]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [h10456, h9898, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11088_1, p11255_1]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [h10456, h10733, h9889, h9891, h9892, h9898, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11088_1, p11255_1]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [hlam, p11255_0]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [h10456, h10733, h7600, h9889, h9891, h9898, hlam, p11088_1, p11255_2]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              rcases p11255_3 (m.d 0 3) (by simp) with h11274 | h11274
                              · linarith only [h11274, h7600, hlam]
                              · linarith only [h11274, h9889, hlam]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [h10456, h9898, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11088_1, p11255_1]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [h9886, hlam, p11255_0]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [h9892, hlam, p11255_0]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [hlam, p11255_0]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [h9898, hlam, p11255_0]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [h10456, hlam, p11255_0]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [h9889, hlam, p11255_0]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [h9895, hlam, p11255_0]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [h10733, h9889, h9891, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11255_1]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [hlam, p11255_0]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [h10733, hlam, p11255_1]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [h9890, hlam, p11255_0]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [h9896, hlam, p11255_0]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              rcases p11255_3 (m.d 0 3) (by simp) with h11290 | h11290
                              · rcases p11255_3 (m.d 1 3) (by simp) with h11291 | h11291
                                · rcases p11255_3 (m.d 2 3) (by simp) with h11292 | h11292
                                  · linarith only [h11292, hlam, p11255_0]
                                  · rcases p11255_3 (m.d 3 4) (by simp) with h11294 | h11294
                                    · linarith only [h10733, h11294, hlam]
                                    · linarith only [h11294, h9898, hlam]
                                · linarith only [h11291, h9892, hlam]
                              · linarith only [h11290, h9886, hlam]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [h9898, hc23, hc35, hlam, hphi, p11255_1]
                            · have p11255_0 := h11255c.1
                              have p11255_1 := h11255c.2.1
                              have p11255_2 := h11255c.2.2.1
                              have p11255_3 := h11255c.2.2.2
                              linarith only [hlam, p11255_0]
                          · linarith only [h10458, h11254, hlam]
                    · linarith only [h11249, h9893, hlam]
                  · linarith only [h11248, h9887, hlam]
                · have p11088_0 := h11088c.1
                  have p11088_1 := h11088c.2.1
                  have p11088_2 := h11088c.2.2.1
                  have p11088_3 := h11088c.2.2.2
                  linarith only [hlam, p11088_0]
              · linarith only [h11087, h9666, hlam]
            · linarith only [h11086, h8836, hlam]
          · linarith only [h11085, h7600, hlam]
        · linarith only [h0, h11084, hlam]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [h9888, hlam, p11037_1]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [h9890, hlam, p11037_0]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [h9891, hlam, p11037_1]
    · have p11037_0 := h11037c.1
      have p11037_1 := h11037c.2.1
      have p11037_2 := h11037c.2.2.1
      have p11037_3 := h11037c.2.2.2
      linarith only [hlam, p11037_0]

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1 (m : N7Model)
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
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9893 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9894 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9895 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9896 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h9897 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h9898 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h10456 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  rcases m.htr 2 4 5 (by decide) (by decide) with h10458 | h10458
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892 h9893 h9894 h9895 h9896 h9897 h9898 h10456 h10458
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892 h9893 h9894 h9895 h9896 h9897 h9898 h10456 h10458

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9893 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9894 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9895 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9896 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h9897 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h9898 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  rcases m.htr 2 3 5 (by decide) (by decide) with h10456 | h10456
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892 h9893 h9894 h9895 h9896 h9897 h9898 h10456
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892 h9893 h9894 h9895 h9896 h9897 h9898 h10456

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9893 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9894 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9895 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9896 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h9897 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  rcases m.htr 2 3 4 (by decide) (by decide) with h9898 | h9898
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892 h9893 h9894 h9895 h9896 h9897 h9898
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892 h9893 h9894 h9895 h9896 h9897 h9898

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9893 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9894 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9895 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9896 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h9897 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  linarith only [h7600, h8836, h9889, h9891, h9892, h9897, hc01, hc12, hlam, hphi]

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9893 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9894 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9895 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9896 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  rcases m.htr 1 4 5 (by decide) (by decide) with h9897 | h9897
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892 h9893 h9894 h9895 h9896 h9897
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892 h9893 h9894 h9895 h9896 h9897

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9893 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9894 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9895 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9896 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  linarith only [h7600, h9890, h9896, hlam]

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9893 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9894 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9895 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  rcases m.htr 1 3 5 (by decide) (by decide) with h9896 | h9896
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892 h9893 h9894 h9895 h9896
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892 h9893 h9894 h9895 h9896

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9893 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9894 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9895 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  linarith only [h7600, h9889, h9895, hlam]

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9893 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9894 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  rcases m.htr 1 3 4 (by decide) (by decide) with h9895 | h9895
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892 h9893 h9894 h9895
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 hg9889 h9890 h9891 h9892 h9893 h9894 h9895

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9893 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9894 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  linarith only [h0, h9888, h9894, hlam]

end R2N4
