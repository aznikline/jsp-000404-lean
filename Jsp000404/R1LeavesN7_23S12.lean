import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_23S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5176000 in
set_option maxHeartbeats 5176000 in
theorem r1l7_12_24_L_I_M_IR_s1_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 4 5 (by decide) (by decide) with h709 | h709
  · rcases m.htr 1 2 3 (by decide) (by decide) with h710 | h710
    · rcases m.htr 1 2 4 (by decide) (by decide) with h711 | h711
      · rcases m.htr 1 2 5 (by decide) (by decide) with h712 | h712
        · rcases m.htr 1 3 4 (by decide) (by decide) with h713 | h713
          · linarith only [h1, h7, h713, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h715 | h715
            · rcases m.htr 2 3 4 (by decide) (by decide) with h716 | h716
              · linarith only [h4, h7, h716, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h718 | h718
                · rcases m.htr 2 4 5 (by decide) (by decide) with h719 | h719
                  · linarith only [h0, h711, h719, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h2, h715, h719, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h722 | h722
                  · linarith only [h0, h711, h722, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h711, h715, h722, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h725 | h725
              · linarith only [h7, h709, h711, h715, h725, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h727 | h727
                · rcases m.htr 2 4 5 (by decide) (by decide) with h728 | h728
                  · linarith only [h711, h715, h728, hlam]
                  · linarith only [h725, h727, h728, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h731 | h731
                  · linarith only [h711, h715, h731, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h733 | h733
                    · rcases h2bigk with h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [hlam, p734_0]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [h0, h711, hc01, hlam, hphi, ht0b, ht45, ht5b, p734_1, u4ehi2]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        rcases p734_3 (m.d 0 2) (by simp) with h737 | h737
                        · rcases p734_3 (m.d 1 2) (by simp) with h738 | h738
                          · linarith only [h0, h738, hlam]
                          · linarith only [h710, h738, hlam]
                        · linarith only [h737, hlam, p734_0]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        rcases p734_3 (m.d 0 2) (by simp) with h742 | h742
                        · rcases p734_3 (m.d 1 2) (by simp) with h743 | h743
                          · linarith only [h0, h743, hlam]
                          · linarith only [h711, h743, hlam]
                        · linarith only [h742, hlam, p734_0]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        rcases p734_3 (m.d 0 2) (by simp) with h747 | h747
                        · rcases p734_3 (m.d 1 2) (by simp) with h748 | h748
                          · linarith only [h0, h748, hlam]
                          · linarith only [h712, h748, hlam]
                        · linarith only [h747, hlam, p734_0]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [h0, hlam, p734_1]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [hlam, p734_0]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        rcases p734_3 (m.d 0 2) (by simp) with h754 | h754
                        · rcases p734_3 (m.d 1 2) (by simp) with h755 | h755
                          · rcases p734_3 (m.d 2 3) (by simp) with h756 | h756
                            · linarith only [h756, hlam, p734_0]
                            · rcases p734_3 (m.d 2 4) (by simp) with h758 | h758
                              · linarith only [h711, h758, hlam]
                              · linarith only [h725, h758, hlam]
                          · linarith only [h755, hlam, p734_0]
                        · linarith only [h4, h754, hlam]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p734_1, u4ehi2]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [h0, h731, hc01, hlam, hphi, ht0b, ht45, ht5b, p734_1, u4ehi2]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [h4, hlam, p734_0]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [h710, hlam, p734_0]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [hlam, p734_0]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [h725, hlam, p734_1]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [h727, hlam, p734_1]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [h5, hlam, p734_0]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [h711, hlam, p734_0]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [h7, h709, h711, h715, hc23, hc34, hlam, hphi, p734_1]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [hlam, p734_0]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [h731, hlam, p734_0]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [h6, hlam, p734_0]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [h712, hlam, p734_0]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [h0, h7, h709, h711, h712, h715, hc01, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p734_1, u4ehi2]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [h0, h712, hc01, hlam, hphi, ht0b, ht45, ht5b, p734_1, u4ehi2]
                      · have p734_0 := h734c.1
                        have p734_1 := h734c.2.1
                        have p734_2 := h734c.2.2.1
                        have p734_3 := h734c.2.2.2
                        linarith only [hlam, p734_0]
                    · linarith only [h7, h709, h733, hlam]
        · linarith only [h0, h6, h711, h712, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h782 | h782
        · rcases m.htr 1 3 4 (by decide) (by decide) with h783 | h783
          · linarith only [h1, h7, h709, h783, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h785 | h785
            · rcases m.htr 2 3 4 (by decide) (by decide) with h786 | h786
              · linarith only [h5, h7, h710, h711, h786, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h788 | h788
                · linarith only [h0, h5, h710, h711, h788, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h790 | h790
                  · linarith only [h0, h5, h711, h782, h790, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h711, h782, h785, h788, h790, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h7, h709, h710, h711, h785, hc23, hc34, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h794 | h794
          · linarith only [h1, h7, h709, h794, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h796 | h796
            · rcases m.htr 2 3 4 (by decide) (by decide) with h797 | h797
              · linarith only [h5, h7, h710, h711, h797, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h799 | h799
                · linarith only [h0, h5, h710, h711, h799, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h801 | h801
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h802 | h802
                    · rcases h2bigk with h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [hlam, p803_0]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        rcases p803_3 (m.d 0 2) (by simp) with h805 | h805
                        · rcases p803_3 (m.d 1 2) (by simp) with h806 | h806
                          · linarith only [h0, h806, hlam]
                          · rcases p803_3 (m.d 2 3) (by simp) with h808 | h808
                            · linarith only [h4, h808, hlam]
                            · rcases p803_3 (m.d 2 4) (by simp) with h810 | h810
                              · linarith only [h5, h810, hlam]
                              · linarith only [h711, h810, hlam]
                        · linarith only [h0, h805, hlam]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [h5, h710, h782, h801, hlam, p803_2]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [h0, h710, h782, h801, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p803_1]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [h0, h710, h782, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p803_1]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [h0, hlam, p803_1]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [hlam, p803_0]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [h6, h7, h709, h782, hc23, hc34, hlam, hphi, p803_1]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [h711, hlam, p803_0]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [h782, hlam, p803_0]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [h4, hlam, p803_0]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [h710, hlam, p803_0]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [hlam, p803_0]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [h797, hlam, p803_1]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [h799, hlam, p803_1]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [h5, hlam, p803_0]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [h0, h5, h710, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p803_1]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        rcases p803_3 (m.d 0 2) (by simp) with h829 | h829
                        · rcases p803_3 (m.d 1 2) (by simp) with h830 | h830
                          · linarith only [h711, h830, hlam]
                          · linarith only [h710, h830, hlam]
                        · linarith only [h4, h829, hlam]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [hlam, p803_0]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [h0, h5, h710, h782, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p803_1]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [h6, hlam, p803_0]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [h710, h799, hc23, hc35, hlam, hphi, p803_1]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        rcases p803_3 (m.d 0 2) (by simp) with h838 | h838
                        · rcases p803_3 (m.d 1 2) (by simp) with h839 | h839
                          · linarith only [h782, h839, hlam]
                          · linarith only [h710, h839, hlam]
                        · linarith only [h4, h838, hlam]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [h801, hlam, p803_1]
                      · have p803_0 := h803c.1
                        have p803_1 := h803c.2.1
                        have p803_2 := h803c.2.2.1
                        have p803_3 := h803c.2.2.2
                        linarith only [hlam, p803_0]
                    · linarith only [h2, h7, h796, h802, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · linarith only [h711, h796, h801, hlam]
            · linarith only [h7, h709, h710, h711, h796, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h848 | h848
      · linarith only [h0, h4, h710, h848, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h850 | h850
        · rcases m.htr 1 3 4 (by decide) (by decide) with h851 | h851
          · linarith only [h4, h7, h710, h851, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h853 | h853
            · rcases m.htr 2 3 4 (by decide) (by decide) with h854 | h854
              · linarith only [h4, h7, h854, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h856 | h856
                · rcases m.htr 2 4 5 (by decide) (by decide) with h857 | h857
                  · linarith only [h4, h7, h710, h850, h857, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · linarith only [h710, h850, h853, h854, h857, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h710, h850, h856, hlam]
            · linarith only [h710, h850, h851, h853, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h862 | h862
          · linarith only [h1, h7, h709, h862, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h864 | h864
            · rcases m.htr 2 3 4 (by decide) (by decide) with h865 | h865
              · linarith only [h4, h7, h865, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h867 | h867
                · rcases m.htr 2 4 5 (by decide) (by decide) with h868 | h868
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h869 | h869
                    · rcases h2bigk with h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [hlam, p870_0]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        rcases p870_3 (m.d 0 2) (by simp) with h872 | h872
                        · rcases p870_3 (m.d 1 2) (by simp) with h873 | h873
                          · linarith only [h0, h873, hlam]
                          · rcases p870_3 (m.d 2 3) (by simp) with h875 | h875
                            · linarith only [h4, h875, hlam]
                            · linarith only [h710, h875, hlam]
                        · linarith only [h0, h872, hlam]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [h0, h867, h869, hc01, hlam, hphi, ht0b, ht45, ht5b, p870_1, u4ehi4]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [h0, h848, h864, hc01, hlam, hphi, ht0b, ht45, ht5b, p870_1, u4ehi4]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        rcases p870_3 (m.d 0 2) (by simp) with h881 | h881
                        · rcases p870_3 (m.d 1 2) (by simp) with h882 | h882
                          · linarith only [h0, h882, hlam]
                          · rcases p870_3 (m.d 2 3) (by simp) with h884 | h884
                            · linarith only [h4, h884, hlam]
                            · linarith only [h867, h884, hlam]
                        · linarith only [h881, hlam, p870_0]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [h0, hlam, p870_1]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [hlam, p870_0]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [h710, hlam, p870_0]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [h848, hlam, p870_0]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [h850, hlam, p870_0]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [h4, hlam, p870_0]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p870_1]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [hlam, p870_0]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [h865, hlam, p870_1]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [h4, h7, h850, hc12, hc34, hlam, hphi, ht23, p870_1]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [h5, hlam, p870_0]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        rcases p870_3 (m.d 0 2) (by simp) with h899 | h899
                        · rcases p870_3 (m.d 1 2) (by simp) with h900 | h900
                          · linarith only [h900, hlam, p870_0]
                          · rcases p870_3 (m.d 2 3) (by simp) with h902 | h902
                            · linarith only [h865, h902, hlam]
                            · linarith only [h710, h902, hlam]
                        · linarith only [h0, h899, hlam]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [h710, hc12, hc24, hlam, hphi, p870_1]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [hlam, p870_0]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [h0, h5, h850, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p870_1]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [h6, hlam, p870_0]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [h4, h7, h867, hc12, hc34, hlam, hphi, ht23, p870_1]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [h867, hlam, p870_0]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [h868, hlam, p870_1]
                      · have p870_0 := h870c.1
                        have p870_1 := h870c.2.1
                        have p870_2 := h870c.2.2.1
                        have p870_3 := h870c.2.2.2
                        linarith only [hlam, p870_0]
                    · linarith only [h4, h7, h864, h867, h869, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h848, h864, h868, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h916 | h916
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h917 | h917
                    · rcases h2bigk with h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [hlam, p918_0]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        rcases p918_3 (m.d 0 2) (by simp) with h920 | h920
                        · rcases p918_3 (m.d 1 2) (by simp) with h921 | h921
                          · linarith only [h0, h921, hlam]
                          · rcases p918_3 (m.d 2 3) (by simp) with h923 | h923
                            · linarith only [h4, h923, hlam]
                            · linarith only [h710, h923, hlam]
                        · linarith only [h0, h920, hlam]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        rcases p918_3 (m.d 0 2) (by simp) with h927 | h927
                        · rcases p918_3 (m.d 1 2) (by simp) with h928 | h928
                          · linarith only [h0, h928, hlam]
                          · rcases p918_3 (m.d 2 3) (by simp) with h930 | h930
                            · linarith only [h930, hlam, p918_0]
                            · rcases p918_3 (m.d 2 4) (by simp) with h932 | h932
                              · linarith only [h5, h932, hlam]
                              · linarith only [h865, h932, hlam]
                        · linarith only [h927, hlam, p918_0]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [h848, h864, hc02, hlam, hphi, ht0b, ht45, ht5b, p918_1, u4ehi4]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        rcases p918_3 (m.d 0 2) (by simp) with h937 | h937
                        · rcases p918_3 (m.d 1 2) (by simp) with h938 | h938
                          · linarith only [h0, h938, hlam]
                          · rcases p918_3 (m.d 2 3) (by simp) with h940 | h940
                            · linarith only [h4, h940, hlam]
                            · rcases p918_3 (m.d 2 4) (by simp) with h942 | h942
                              · linarith only [h5, h942, hlam]
                              · linarith only [h916, h942, hlam]
                        · linarith only [h937, hlam, p918_0]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [h0, hlam, p918_1]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [hlam, p918_0]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [h710, hlam, p918_0]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [h848, hlam, p918_0]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [h850, hlam, p918_0]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [h4, hlam, p918_0]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p918_1]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [hlam, p918_0]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [h865, hlam, p918_1]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [h867, hlam, p918_1]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [h5, hlam, p918_0]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        rcases p918_3 (m.d 0 2) (by simp) with h957 | h957
                        · rcases p918_3 (m.d 1 2) (by simp) with h958 | h958
                          · linarith only [h958, hlam, p918_0]
                          · rcases p918_3 (m.d 2 3) (by simp) with h960 | h960
                            · linarith only [h865, h960, hlam]
                            · linarith only [h710, h960, hlam]
                        · linarith only [h0, h957, hlam]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [h0, h5, h710, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p918_1]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [hlam, p918_0]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [h0, h5, h710, h867, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p918_1]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [h6, hlam, p918_0]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        rcases p918_3 (m.d 0 2) (by simp) with h968 | h968
                        · rcases p918_3 (m.d 1 2) (by simp) with h969 | h969
                          · linarith only [h969, hlam, p918_0]
                          · rcases p918_3 (m.d 2 3) (by simp) with h971 | h971
                            · linarith only [h867, h971, hlam]
                            · linarith only [h710, h971, hlam]
                        · linarith only [h0, h968, hlam]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [h710, hc12, hc25, hlam, hphi, p918_1]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [h916, hlam, p918_1]
                      · have p918_0 := h918c.1
                        have p918_1 := h918c.2.1
                        have p918_2 := h918c.2.2.1
                        have p918_3 := h918c.2.2.2
                        linarith only [hlam, p918_0]
                    · linarith only [h2, h7, h864, h917, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h848, h864, h916, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h980 | h980
              · linarith only [h7, h709, h864, h980, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h982 | h982
                · rcases m.htr 2 4 5 (by decide) (by decide) with h983 | h983
                  · linarith only [h0, h5, h864, h983, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                  · linarith only [h7, h709, h848, h983, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h986 | h986
                  · linarith only [h0, h5, h864, h986, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                  · linarith only [h7, h709, h848, h986, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h989 | h989
    · rcases m.htr 1 2 4 (by decide) (by decide) with h990 | h990
      · rcases m.htr 1 2 5 (by decide) (by decide) with h991 | h991
        · rcases m.htr 1 3 4 (by decide) (by decide) with h992 | h992
          · linarith only [h1, h7, h709, h992, hc45, hlam, hphi, u4ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h994 | h994
            · linarith only [h2, h709, h994, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h996 | h996
              · linarith only [h1, h7, h989, h996, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h998 | h998
                · rcases m.htr 2 4 5 (by decide) (by decide) with h999 | h999
                  · linarith only [h709, h990, h999, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                  · linarith only [h996, h998, h999, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1002 | h1002
                  · linarith only [h0, h1002, h2, h5, h709, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1004 | h1004
                    · rcases h2bigk with h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [hlam, p1005_0]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [h0, h990, hc01, hlam, hphi, ht0b, ht45, ht5b, p1005_1, u4ehi2]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        rcases p1005_3 (m.d 0 2) (by simp) with h1008 | h1008
                        · rcases p1005_3 (m.d 1 2) (by simp) with h1009 | h1009
                          · linarith only [h0, h1009, hlam]
                          · linarith only [h1009, h989, hlam]
                        · linarith only [h1008, hlam, p1005_0]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        rcases p1005_3 (m.d 0 2) (by simp) with h1013 | h1013
                        · rcases p1005_3 (m.d 1 2) (by simp) with h1014 | h1014
                          · linarith only [h0, h1014, hlam]
                          · linarith only [h1014, h990, hlam]
                        · linarith only [h1013, hlam, p1005_0]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        rcases p1005_3 (m.d 0 2) (by simp) with h1018 | h1018
                        · rcases p1005_3 (m.d 1 2) (by simp) with h1019 | h1019
                          · linarith only [h0, h1019, hlam]
                          · linarith only [h1019, h991, hlam]
                        · linarith only [h1018, hlam, p1005_0]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [h0, hlam, p1005_1]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [hlam, p1005_0]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        rcases p1005_3 (m.d 0 2) (by simp) with h1025 | h1025
                        · rcases p1005_3 (m.d 1 2) (by simp) with h1026 | h1026
                          · rcases p1005_3 (m.d 2 3) (by simp) with h1027 | h1027
                            · linarith only [h1027, hlam, p1005_0]
                            · rcases p1005_3 (m.d 2 4) (by simp) with h1029 | h1029
                              · linarith only [h1029, h990, hlam]
                              · linarith only [h1029, h996, hlam]
                          · linarith only [h1026, hlam, p1005_0]
                        · linarith only [h1025, h4, hlam]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p1005_1, u4ehi2]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [h0, h1002, hc01, hlam, hphi, ht0b, ht45, ht5b, p1005_1, u4ehi2]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [h4, hlam, p1005_0]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [h989, hlam, p1005_0]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [hlam, p1005_0]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [h996, hlam, p1005_1]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [h998, hlam, p1005_1]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [h5, hlam, p1005_0]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [h990, hlam, p1005_0]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [h1004, h2, h709, h990, hc23, hc34, hlam, hphi, p1005_1]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [hlam, p1005_0]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [h1002, hlam, p1005_0]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [h6, hlam, p1005_0]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [h991, hlam, p1005_0]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [h1004, h6, h709, hc23, hc34, hlam, hphi, p1005_1]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [h0, h991, hc01, hlam, hphi, ht0b, ht45, ht5b, p1005_1, u4ehi2]
                      · have p1005_0 := h1005c.1
                        have p1005_1 := h1005c.2.1
                        have p1005_2 := h1005c.2.2.1
                        have p1005_3 := h1005c.2.2.2
                        linarith only [hlam, p1005_0]
                    · rcases h2bigk with h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h0, h990, hc01, hlam, hphi, ht0b, ht45, ht5b, p1051_1, u4ehi2]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        rcases p1051_3 (m.d 0 2) (by simp) with h1054 | h1054
                        · rcases p1051_3 (m.d 1 2) (by simp) with h1055 | h1055
                          · linarith only [h0, h1055, hlam]
                          · linarith only [h1055, h989, hlam]
                        · linarith only [h1054, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        rcases p1051_3 (m.d 0 2) (by simp) with h1059 | h1059
                        · rcases p1051_3 (m.d 1 2) (by simp) with h1060 | h1060
                          · linarith only [h0, h1060, hlam]
                          · linarith only [h1060, h990, hlam]
                        · linarith only [h1059, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        rcases p1051_3 (m.d 0 2) (by simp) with h1064 | h1064
                        · rcases p1051_3 (m.d 1 2) (by simp) with h1065 | h1065
                          · linarith only [h0, h1065, hlam]
                          · linarith only [h1065, h991, hlam]
                        · linarith only [h1064, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h0, hlam, p1051_1]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        rcases p1051_3 (m.d 0 2) (by simp) with h1071 | h1071
                        · rcases p1051_3 (m.d 1 2) (by simp) with h1072 | h1072
                          · rcases p1051_3 (m.d 2 3) (by simp) with h1073 | h1073
                            · linarith only [h1073, hlam, p1051_0]
                            · rcases p1051_3 (m.d 2 4) (by simp) with h1075 | h1075
                              · linarith only [h1075, h990, hlam]
                              · linarith only [h1075, h996, hlam]
                          · linarith only [h1072, hlam, p1051_0]
                        · linarith only [h1071, h4, hlam]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p1051_1, u4ehi2]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h0, h1002, hc01, hlam, hphi, ht0b, ht45, ht5b, p1051_1, u4ehi2]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h4, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h989, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h996, hlam, p1051_1]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h998, hlam, p1051_1]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h5, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h990, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h1004, h2, h7, h990, hc23, hc45, hlam, hphi, ht34, p1051_1]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h1002, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h6, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h991, hlam, p1051_0]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h0, h991, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1051_1]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [h0, h991, hc01, hlam, hphi, ht0b, ht45, ht5b, p1051_1, u4ehi2]
                      · have p1051_0 := h1051c.1
                        have p1051_1 := h1051c.2.1
                        have p1051_2 := h1051c.2.2.1
                        have p1051_3 := h1051c.2.2.2
                        linarith only [hlam, p1051_0]
        · linarith only [h0, h6, h990, h991, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
      · linarith only [h5, h709, h989, h990, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1099 | h1099
      · linarith only [h1099, h4, h7, h989, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1101 | h1101
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1102 | h1102
          · linarith only [h1102, h4, h7, h709, h989, hc45, hlam, hphi, u4ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1104 | h1104
            · linarith only [h1101, h1104, h4, h7, h709, h989, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h1101, h1104, h4, h7, h709, h989, hc45, hlam, hphi, u4ehi1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1107 | h1107
          · linarith only [h1107, h4, h7, h989, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1109 | h1109
            · linarith only [h1109, h2, h709, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1111 | h1111
              · linarith only [h1111, h4, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1113 | h1113
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1114 | h1114
                  · linarith only [h1114, h5, h709, hlam]
                  · linarith only [h1111, h1113, h1114, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1117 | h1117
                  · linarith only [h0, h1117, h5, h709, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1119 | h1119
                    · linarith only [h1119, h4, h7, h709, h989, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1119, h4, h7, h989, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5176000 in
set_option maxHeartbeats 5176000 in
theorem r1l7_12_24_L_I_M_IR_s1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_12_24_L_I_M_IR_s1_x0_x0_x0_x0_x0_x0 m hb2 hb4 hg0 hg1 h2 h3 h4 h5 h6 h7
  · exact r1l7_12_24_L_I_M_IR_s1_x0_x0_x0_x0_x0_x1 m hb2 hb4 hg0 hg1 h2 h3 h4 h5 h6 h7

set_option maxHeartbeats 5176000 in
set_option maxHeartbeats 5176000 in
theorem r1l7_12_24_L_I_M_IR_s1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 3 4 (by decide) (by decide) with h1122 | h1122
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1123 | h1123
    · linarith only [h1122, h1123, h4, h6, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1125 | h1125
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1126 | h1126
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1127 | h1127
          · linarith only [h0, h1127, h6, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1129 | h1129
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1130 | h1130
              · linarith only [h1123, h1130, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1132 | h1132
                · linarith only [h0, h1125, h1132, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1134 | h1134
                  · linarith only [h1, h1129, h1132, h1134, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1, h1129, h1132, h1134, h4, h6, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1137 | h1137
              · linarith only [h1122, h1123, h1129, h1137, h4, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1139 | h1139
                · linarith only [h1129, h1139, h4, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1141 | h1141
                  · linarith only [h1122, h1125, h1129, h1141, h4, h6, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h1122, h1125, h1129, h1141, h4, h6, hc23, hc35, hlam, hphi]
        · linarith only [h1126, h5, h6, hc12, hc25, hlam, hphi]
      · linarith only [h1125, h4, h6, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1146 | h1146
    · linarith only [h1146, h5, h6, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1148 | h1148
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1149 | h1149
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1150 | h1150
          · linarith only [h0, h1150, h6, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1152 | h1152
            · linarith only [h1, h1122, h1152, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1154 | h1154
              · linarith only [h1146, h1154, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1156 | h1156
                · linarith only [h1, h1122, h1156, h4, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1158 | h1158
                  · linarith only [h0, h1, h1122, h1148, h1149, h1158, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1160 | h1160
                    · linarith only [h0, h1146, h1149, h1160, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · linarith only [h0, h1149, h1160, h6, hc45, hlam, hphi, u4ehi2]
        · linarith only [h1149, h5, h6, hc12, hc25, hlam, hphi]
      · linarith only [h1148, h4, h6, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 5176000 in
set_option maxHeartbeats 5176000 in
theorem r1l7_12_24_L_I_M_IR_s1_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_12_24_L_I_M_IR_s1_x0_x0_x0_x0_x0 m hb2 hb4 hg0 hg1 h2 h3 h4 h5 h6
  · exact r1l7_12_24_L_I_M_IR_s1_x0_x0_x0_x0_x1 m hb2 hb4 hg0 hg1 h2 h3 h4 h5 h6

set_option maxHeartbeats 5176000 in
set_option maxHeartbeats 5176000 in
theorem r1l7_12_24_L_I_M_IR_s1_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 5 (by decide) (by decide) with h1165 | h1165
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1166 | h1166
    · linarith only [h1166, h4, h5, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1168 | h1168
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1169 | h1169
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1170 | h1170
          · linarith only [h0, h1165, h1170, h5, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1172 | h1172
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1173 | h1173
              · linarith only [h1, h1166, h1168, h1173, h4, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1175 | h1175
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1176 | h1176
                  · linarith only [h0, h1166, h1169, h1176, h5, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1178 | h1178
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1179 | h1179
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1180 | h1180
                        · linarith only [h1176, h1178, h1180, h4, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · linarith only [h0, h1169, h1172, h1176, h1178, h1179, h1180, h3, h5, hc05, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h1169, h1175, h1178, h1179, h2, h5, hc04, hc35, hlam, hphi, ht0b, ht5b]
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
                            linarith only [h1172, h1176, h1184, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1186_1, u4ehi4]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1176, h5, hc23, hc34, hlam, hphi, p1186_1]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h5, hlam, p1186_0]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1176, h1184, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1186_1, u4ehi4]
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
                            linarith only [h0, h1176, h5, hc23, hc34, hlam, hphi, p1186_1]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1170, hlam, p1186_0]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h0, h1176, h1184, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1186_1, u4ehi4]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h4, hlam, p1186_0]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1169, hlam, p1186_0]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [hlam, p1186_0]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1176, hlam, p1186_1]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1178, hlam, p1186_1]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1176, h4, hc23, hc34, hlam, hphi, p1186_1]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1169, h1176, hc23, hc34, hlam, hphi, p1186_1]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            rcases p1186_3 (m.d 0 2) (by simp) with h1204 | h1204
                            · linarith only [h1204, h5, hlam]
                            · linarith only [h1204, h4, hlam]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [hlam, p1186_0]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            rcases p1186_3 (m.d 0 2) (by simp) with h1208 | h1208
                            · linarith only [h1208, h5, hlam]
                            · linarith only [h1165, h1208, hlam]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1165, hlam, p1186_0]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h1172, hlam, p1186_0]
                          · have p1186_0 := h1186c.1
                            have p1186_1 := h1186c.2.1
                            have p1186_2 := h1186c.2.2.1
                            have p1186_3 := h1186c.2.2.2
                            linarith only [h0, h1172, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1186_1]
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
                        · linarith only [h0, h1172, h1176, h1184, h1185, h5, hlam]
                      · linarith only [h1184, h4, h5, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h1166, h1168, h1169, h1170, h1175, hc23, hc34, hlam, hphi]
            · linarith only [h1165, h1169, h1172, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
        · linarith only [h1169, h4, h5, hc12, hc24, hlam, hphi]
      · linarith only [h1165, h1168, h5, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1222 | h1222
    · linarith only [h1222, h4, h5, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1224 | h1224
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1225 | h1225
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1226 | h1226
          · linarith only [h0, h1226, h5, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1228 | h1228
            · linarith only [h0, h1165, h1228, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1230 | h1230
              · linarith only [h1, h1222, h1230, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1232 | h1232
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1233 | h1233
                  · linarith only [h0, h1, h1222, h1225, h1233, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1235 | h1235
                    · linarith only [h1165, h1235, h4, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1237 | h1237
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1238 | h1238
                        · rcases h2bigk with h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1165, h1237, hc12, hc24, hlam, hphi, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1165, h1233, h1237, hc23, hc34, hlam, hphi, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h5, hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1165, hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h0, hlam, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h0, h1165, h1233, h1237, hc23, hc34, hlam, hphi, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1226, hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1228, hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h4, hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1225, hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1233, hlam, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1235, hlam, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1233, h4, hc23, hc34, hlam, hphi, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1225, h1233, hc23, hc34, hlam, hphi, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            rcases p1239_3 (m.d 0 2) (by simp) with h1257 | h1257
                            · linarith only [h1257, h5, hlam]
                            · linarith only [h1257, h4, hlam]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h0, h1165, h1225, h1233, hc23, hc34, hlam, hphi, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h0, h1225, h1235, hc23, hc35, hlam, hphi, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1225, h1235, hc23, hc35, hlam, hphi, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            rcases p1239_3 (m.d 0 2) (by simp) with h1264 | h1264
                            · linarith only [h1165, h1264, hlam]
                            · linarith only [h1264, h4, hlam]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1237, hlam, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [hlam, p1239_0]
                        · linarith only [h1232, h1233, h1238, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h1232, h1237, h2, h5, hlam]
                · linarith only [h1222, h1224, h1225, h1226, h1232, hc23, hc34, hlam, hphi]
        · linarith only [h1165, h1225, h4, hc12, hc25, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1273 | h1273
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1274 | h1274
          · linarith only [h0, h1274, h5, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1276 | h1276
            · linarith only [h0, h1165, h1276, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1278 | h1278
              · linarith only [h1, h1222, h1278, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1280 | h1280
                · linarith only [h1224, h1280, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1282 | h1282
                  · linarith only [h0, h1, h1222, h1273, h1282, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1284 | h1284
                    · linarith only [h1165, h1284, h4, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1286 | h1286
                      · linarith only [h0, h1224, h1273, h1282, h1286, h5, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h1273, h1286, h5, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h1273, h4, h5, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5176000 in
set_option maxHeartbeats 5176000 in
theorem r1l7_12_24_L_I_M_IR_s1_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_12_24_L_I_M_IR_s1_x0_x0_x0_x0 m hb2 hb4 hg0 hg1 h2 h3 h4 h5
  · exact r1l7_12_24_L_I_M_IR_s1_x0_x0_x0_x1 m hb2 hb4 hg0 hg1 h2 h3 h4 h5

set_option maxHeartbeats 5176000 in
set_option maxHeartbeats 5176000 in
theorem r1l7_12_24_L_I_M_IR_s1_x0_x0_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1290 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 5 (by decide) (by decide) with h1291 | h1291
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1292 | h1292
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1293 | h1293
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1294 | h1294
        · linarith only [h1290, h1294, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1296 | h1296
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1297 | h1297
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1298 | h1298
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1299 | h1299
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1300 | h1300
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1301 | h1301
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1302 | h1302
                      · linarith only [h1290, h1302, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h1299, h1302, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h1290, h1299, h1301, h2, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · linarith only [h1, h1290, h1298, h1299, h1300, h2, h4, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h1290, h1293, h1299, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h1290, h1292, h1294, h1296, h1298, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · linarith only [h1291, h1296, h1297, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
          · linarith only [h1290, h1296, h4, hc12, hc23, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1311 | h1311
        · linarith only [h1290, h1311, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1313 | h1313
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1314 | h1314
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1315 | h1315
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1316 | h1316
                · linarith only [h1293, h1316, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1318 | h1318
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1319 | h1319
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1320 | h1320
                      · linarith only [h0, h1293, h1313, h1320, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1322 | h1322
                        · linarith only [h1293, h1313, h1318, h1322, h2, hlam]
                        · rcases h2bigk with h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p1324_1]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h4, hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1318, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1324_1, u4ehi3]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1318, h1320, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1324_1, u4ehi3]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h0, hlam, p1324_1]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1311, hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h0, h1318, hc01, hlam, hphi, ht0b, ht45, ht5b, p1324_1, u4ehi3]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h0, h1318, h1320, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1324_1, u4ehi3]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1290, h1318, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1324_1, u4ehi3]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1313, h1318, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1324_1, u4ehi3]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            rcases p1324_3 (m.d 0 2) (by simp) with h1338 | h1338
                            · linarith only [h1338, h4, hlam]
                            · linarith only [h1290, h1338, hlam]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            rcases p1324_3 (m.d 0 2) (by simp) with h1341 | h1341
                            · linarith only [h1341, h4, hlam]
                            · linarith only [h1291, h1341, hlam]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1290, hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1313, hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1318, hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1320, hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1291, hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1314, hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1319, hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h0, h1314, h1318, hc02, hlam, hphi, ht0b, ht45, ht5b, p1324_1, u4ehi3]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [hlam, p1324_0]
                    · linarith only [h1290, h1318, h1319, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h1313, h1318, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
              · linarith only [h1292, h1293, h1311, h1313, h1315, hc45, hlam, hphi, u4ehi2]
            · linarith only [h1291, h1313, h1314, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
          · linarith only [h1290, h1313, h4, hc12, hc23, hlam, hphi]
    · linarith only [h1290, h1292, h4, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1360 | h1360
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1361 | h1361
      · linarith only [h1290, h1291, h1361, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1363 | h1363
        · linarith only [h0, h1363, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1365 | h1365
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1366 | h1366
            · linarith only [h0, h1291, h1366, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1368 | h1368
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1369 | h1369
                · linarith only [h1361, h1369, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1371 | h1371
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1372 | h1372
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1373 | h1373
                      · linarith only [h1290, h1291, h1361, h1373, hlam]
                      · linarith only [h0, h1291, h1365, h1371, h1373, hc45, hlam, hphi, u4ehi3]
                    · linarith only [h0, h1365, h1371, h1372, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h1365, h1371, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
              · linarith only [h1360, h1363, h1365, h1368, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
          · linarith only [h1290, h1291, h1365, hc12, hc25, hlam, hphi]
    · linarith only [h1290, h1360, h4, hlam]

set_option maxHeartbeats 5176000 in
set_option maxHeartbeats 5176000 in
theorem r1l7_12_24_L_I_M_IR_s1_x0_x0_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1290 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1381 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 3 4 (by decide) (by decide) with h1382 | h1382
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1383 | h1383
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1384 | h1384
      · linarith only [h0, h1381, h1383, h1384, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1386 | h1386
        · linarith only [h0, h1290, h1386, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1388 | h1388
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1389 | h1389
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1390 | h1390
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1391 | h1391
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1392 | h1392
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1393 | h1393
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1394 | h1394
                      · linarith only [h1, h1389, h1394, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h1290, h1388, h1393, h1394, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h1, h1290, h1389, h1390, h1393, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h1290, h1381, h1391, h1392, hlam]
                · linarith only [h1381, h1382, h1390, h1391, h3, h4, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h1386, h1388, h1390, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1401 | h1401
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1402 | h1402
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1403 | h1403
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1404 | h1404
                    · linarith only [h1382, h1384, h1388, h1389, h1404, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h1401, h1404, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h1382, h1384, h1389, h1403, h4, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h1382, h1402, h4, hlam]
              · linarith only [h1384, h1388, h1389, h1401, hlam]
          · linarith only [h1381, h1388, h4, hc12, hc23, hlam, hphi]
    · linarith only [h1290, h1381, h1383, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1412 | h1412
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1413 | h1413
      · linarith only [h0, h1413, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1415 | h1415
        · linarith only [h1, h1290, h1382, h1413, h1415, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1417 | h1417
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1418 | h1418
            · linarith only [h1, h1382, h1418, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1420 | h1420
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1421 | h1421
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1422 | h1422
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1423 | h1423
                    · linarith only [h1381, h1382, h1421, h1423, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h1382, h1417, h1420, h1421, h1423, h2, h4, hc04, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1381, h1382, h1420, h1421, h1422, h3, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1427 | h1427
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1428 | h1428
                    · linarith only [h1381, h1421, h1428, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h1290, h1417, h1420, h1428, h3, hc01, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h1417, h1427, h4, hlam]
              · linarith only [h1413, h1417, h1418, h1420, hlam]
          · linarith only [h1381, h1417, h4, hc12, hc23, hlam, hphi]
    · linarith only [h1381, h1382, h1412, h4, hlam]

end R2N4
