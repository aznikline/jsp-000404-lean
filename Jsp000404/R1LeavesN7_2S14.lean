import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9250 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9251 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9252 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  have h9250 := hg9250
  rcases m.htr 1 2 3 (by decide) (by decide) with h10694 | h10694
  · linarith only [h0, h10694, h4, hlam]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h10696 | h10696
    · linarith only [h0, h10696, h7337, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h10698 | h10698
      · linarith only [h0, h10698, h8360, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h10700 | h10700
        · rcases m.htr 1 3 5 (by decide) (by decide) with h10701 | h10701
          · rcases m.htr 1 4 5 (by decide) (by decide) with h10702 | h10702
            · linarith only [h10702, h2, h9252, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h10704 | h10704
              · rcases m.htr 2 3 5 (by decide) (by decide) with h10705 | h10705
                · rcases m.htr 2 4 5 (by decide) (by decide) with h10706 | h10706
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h10707 | h10707
                    · linarith only [h10700, h10707, h2, h9252, hlam]
                    · rcases h0bigk with h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c | h10709c
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [hlam, p10709_0]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        rcases p10709_3 (m.d 0 1) (by simp) with h10711 | h10711
                        · rcases p10709_3 (m.d 0 2) (by simp) with h10712 | h10712
                          · linarith only [h0, h10712, hlam]
                          · rcases p10709_3 (m.d 0 3) (by simp) with h10714 | h10714
                            · linarith only [h1, h10714, hlam]
                            · linarith only [h10714, h4, hlam]
                        · linarith only [h0, h10711, hlam]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        rcases p10709_3 (m.d 0 1) (by simp) with h10718 | h10718
                        · rcases p10709_3 (m.d 0 2) (by simp) with h10719 | h10719
                          · linarith only [h0, h10719, hlam]
                          · rcases p10709_3 (m.d 0 3) (by simp) with h10721 | h10721
                            · linarith only [h1, h10721, hlam]
                            · rcases p10709_3 (m.d 0 4) (by simp) with h10723 | h10723
                              · linarith only [h10723, h2, hlam]
                              · rcases p10709_3 (m.d 0 5) (by simp) with h10725 | h10725
                                · linarith only [h10725, h3, hlam]
                                · rcases h2bigk with h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c | h10727c
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [hlam, p10727_0]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [h10704, h10706, h7337, h9252, hc12, hc23, hlam, hphi, p10727_1]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [h4, hlam, p10727_0]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [h7337, hlam, p10727_0]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [h8360, hlam, p10727_0]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [h0, hlam, p10727_0]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [hlam, p10727_0]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [h10694, hlam, p10727_0]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [h10696, hlam, p10727_0]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [h10698, hlam, p10727_0]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    rcases p10727_3 (m.d 0 2) (by simp) with h10738 | h10738
                                    · linarith only [h10738, hlam, p10727_0]
                                    · rcases p10727_3 (m.d 1 2) (by simp) with h10740 | h10740
                                      · linarith only [h10694, h10740, hlam]
                                      · rcases p10727_3 (m.d 2 3) (by simp) with h10742 | h10742
                                        · rcases p10727_3 (m.d 2 4) (by simp) with h10743 | h10743
                                          · linarith only [h10704, h10743, hlam]
                                          · linarith only [h10743, h7337, hlam]
                                        · linarith only [h10742, hlam, p10727_0]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    rcases p10727_3 (m.d 0 2) (by simp) with h10747 | h10747
                                    · linarith only [h10747, h4, hlam]
                                    · linarith only [h0, h10747, hlam]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [hlam, p10727_0]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [h10706, h7337, h9252, hc02, hc23, hlam, hphi, p10727_1]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [h0, h8360, hc12, hc23, hlam, hphi, p10727_1]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    rcases p10727_3 (m.d 0 2) (by simp) with h10753 | h10753
                                    · linarith only [h10753, hlam, p10727_0]
                                    · rcases p10727_3 (m.d 1 2) (by simp) with h10755 | h10755
                                      · linarith only [h10696, h10755, hlam]
                                      · rcases p10727_3 (m.d 2 3) (by simp) with h10757 | h10757
                                        · rcases p10727_3 (m.d 2 4) (by simp) with h10758 | h10758
                                          · rcases p10727_3 (m.d 2 5) (by simp) with h10759 | h10759
                                            · linarith only [h10706, h10759, hlam]
                                            · linarith only [h10759, h8360, hlam]
                                          · linarith only [h10758, hlam, p10727_0]
                                        · linarith only [h10757, h4, hlam]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    rcases p10727_3 (m.d 0 2) (by simp) with h10764 | h10764
                                    · linarith only [h10764, h7337, hlam]
                                    · linarith only [h0, h10764, hlam]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [h10704, hlam, p10727_1]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [hlam, p10727_0]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [h0, h10706, h7337, h9252, hc12, hc24, hlam, hphi, p10727_1]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    rcases p10727_3 (m.d 0 2) (by simp) with h10770 | h10770
                                    · linarith only [h10770, hlam, p10727_0]
                                    · rcases p10727_3 (m.d 1 2) (by simp) with h10772 | h10772
                                      · linarith only [h10698, h10772, hlam]
                                      · rcases p10727_3 (m.d 2 3) (by simp) with h10774 | h10774
                                        · rcases p10727_3 (m.d 2 4) (by simp) with h10775 | h10775
                                          · rcases p10727_3 (m.d 2 5) (by simp) with h10776 | h10776
                                            · rcases h3bigk with h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [hlam, p10777_0]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p10709_1, p10777_1]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [h4, hlam, p10777_1]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10709_1, p10777_1]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [hc01, hc35, hlam, hphi, ht0b, ht5b, p10709_1, p10777_1]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [h1, hlam, p10777_0]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [hlam, p10777_0]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [h10694, hlam, p10777_1]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10777_1]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p10709_1, p10777_1]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [h0, h4, hc12, hc23, hlam, hphi, p10777_1]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [h10694, hc12, hc23, hlam, hphi, p10777_1]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [hlam, p10777_0]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                rcases p10777_3 (m.d 0 3) (by simp) with h10791 | h10791
                                                · linarith only [h10791, h4, hlam]
                                                · linarith only [h10791, h9250, hlam]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                rcases p10777_3 (m.d 0 3) (by simp) with h10794 | h10794
                                                · linarith only [h10794, h4, hlam]
                                                · linarith only [h10794, h9251, hlam]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [h9250, hlam, p10777_0]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [h10700, hlam, p10777_0]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [h10704, hlam, p10777_0]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [hlam, p10777_0]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [h10707, hlam, p10777_1]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [h9251, hlam, p10777_0]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [h10701, hlam, p10777_0]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [h10705, hlam, p10777_0]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [h1, h10701, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p10777_1]
                                              · have p10777_0 := h10777c.1
                                                have p10777_1 := h10777c.2.1
                                                have p10777_2 := h10777c.2.2.1
                                                have p10777_3 := h10777c.2.2.2
                                                linarith only [hlam, p10777_0]
                                            · linarith only [h10776, hlam, p10727_0]
                                          · linarith only [h10775, h7337, hlam]
                                        · linarith only [h10774, h4, hlam]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    rcases p10727_3 (m.d 0 2) (by simp) with h10810 | h10810
                                    · linarith only [h10810, h8360, hlam]
                                    · linarith only [h0, h10810, hlam]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [h10705, hlam, p10727_1]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [h10706, hlam, p10727_0]
                                  · have p10727_0 := h10727c.1
                                    have p10727_1 := h10727c.2.1
                                    have p10727_2 := h10727c.2.2.1
                                    have p10727_3 := h10727c.2.2.2
                                    linarith only [hlam, p10727_0]
                        · linarith only [h1, h10718, hlam]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        rcases p10709_3 (m.d 0 1) (by simp) with h10817 | h10817
                        · rcases p10709_3 (m.d 0 2) (by simp) with h10818 | h10818
                          · linarith only [h0, h10818, hlam]
                          · rcases p10709_3 (m.d 0 3) (by simp) with h10820 | h10820
                            · linarith only [h1, h10820, hlam]
                            · linarith only [h10820, h9250, hlam]
                        · linarith only [h10817, h2, hlam]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        rcases p10709_3 (m.d 0 1) (by simp) with h10824 | h10824
                        · rcases p10709_3 (m.d 0 2) (by simp) with h10825 | h10825
                          · linarith only [h0, h10825, hlam]
                          · rcases p10709_3 (m.d 0 3) (by simp) with h10827 | h10827
                            · linarith only [h1, h10827, hlam]
                            · linarith only [h10827, h9251, hlam]
                        · linarith only [h10824, h3, hlam]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [h0, hlam, p10709_0]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [hlam, p10709_0]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [h4, hlam, p10709_0]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [h7337, hlam, p10709_1]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [h8360, hlam, p10709_0]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [h1, hlam, p10709_1]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        rcases p10709_3 (m.d 0 1) (by simp) with h10837 | h10837
                        · rcases p10709_3 (m.d 0 2) (by simp) with h10838 | h10838
                          · linarith only [h10838, h4, hlam]
                          · rcases p10709_3 (m.d 0 3) (by simp) with h10840 | h10840
                            · rcases p10709_3 (m.d 0 4) (by simp) with h10841 | h10841
                              · linarith only [h10841, h9250, hlam]
                              · linarith only [h10841, h7337, hlam]
                            · linarith only [h10840, h4, hlam]
                        · linarith only [h0, h10837, hlam]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [hlam, p10709_0]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        rcases p10709_3 (m.d 0 1) (by simp) with h10847 | h10847
                        · rcases p10709_3 (m.d 0 2) (by simp) with h10848 | h10848
                          · linarith only [h10848, h4, hlam]
                          · rcases p10709_3 (m.d 0 3) (by simp) with h10850 | h10850
                            · rcases p10709_3 (m.d 0 4) (by simp) with h10851 | h10851
                              · linarith only [h10851, h9250, hlam]
                              · rcases p10709_3 (m.d 0 5) (by simp) with h10853 | h10853
                                · linarith only [h10853, h9251, hlam]
                                · linarith only [h10853, h9252, hlam]
                            · linarith only [h10850, h9250, hlam]
                        · linarith only [h10847, h2, hlam]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        rcases p10709_3 (m.d 0 1) (by simp) with h10858 | h10858
                        · rcases p10709_3 (m.d 0 2) (by simp) with h10859 | h10859
                          · linarith only [h10859, h4, hlam]
                          · rcases p10709_3 (m.d 0 3) (by simp) with h10861 | h10861
                            · rcases p10709_3 (m.d 0 4) (by simp) with h10862 | h10862
                              · linarith only [h10862, h9250, hlam]
                              · rcases p10709_3 (m.d 0 5) (by simp) with h10864 | h10864
                                · linarith only [h10864, h9251, hlam]
                                · rcases h2bigk with h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c | h10866c
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [hlam, p10866_0]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [h7337, h9252, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10709_1, p10866_1]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [h4, hlam, p10866_0]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [h7337, hlam, p10866_0]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [h8360, hlam, p10866_0]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [h0, hlam, p10866_0]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [hlam, p10866_0]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [h10694, hlam, p10866_0]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [h10696, hlam, p10866_0]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [h10698, hlam, p10866_0]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    rcases p10866_3 (m.d 0 2) (by simp) with h10877 | h10877
                                    · linarith only [h10877, hlam, p10866_0]
                                    · rcases p10866_3 (m.d 1 2) (by simp) with h10879 | h10879
                                      · linarith only [h10694, h10879, hlam]
                                      · rcases p10866_3 (m.d 2 3) (by simp) with h10881 | h10881
                                        · rcases p10866_3 (m.d 2 4) (by simp) with h10882 | h10882
                                          · linarith only [h10704, h10882, hlam]
                                          · linarith only [h10882, h7337, hlam]
                                        · linarith only [h10881, hlam, p10866_0]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    rcases p10866_3 (m.d 0 2) (by simp) with h10886 | h10886
                                    · linarith only [h10886, h4, hlam]
                                    · linarith only [h0, h10886, hlam]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [hlam, p10866_0]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [h7337, hc02, hc23, hlam, hphi, p10866_1]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [h0, h8360, hc12, hc23, hlam, hphi, p10866_1]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    rcases p10866_3 (m.d 0 2) (by simp) with h10892 | h10892
                                    · linarith only [h10892, hlam, p10866_0]
                                    · rcases p10866_3 (m.d 1 2) (by simp) with h10894 | h10894
                                      · linarith only [h10696, h10894, hlam]
                                      · rcases p10866_3 (m.d 2 3) (by simp) with h10896 | h10896
                                        · rcases p10866_3 (m.d 2 4) (by simp) with h10897 | h10897
                                          · rcases p10866_3 (m.d 2 5) (by simp) with h10898 | h10898
                                            · linarith only [h10706, h10898, hlam]
                                            · linarith only [h10898, h8360, hlam]
                                          · linarith only [h10897, hlam, p10866_0]
                                        · linarith only [h10896, h4, hlam]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    rcases p10866_3 (m.d 0 2) (by simp) with h10903 | h10903
                                    · linarith only [h10903, h7337, hlam]
                                    · linarith only [h0, h10903, hlam]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [h10704, hlam, p10866_1]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [hlam, p10866_0]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [h0, h10706, h7337, h9252, hc12, hc24, hlam, hphi, p10866_1]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    rcases p10866_3 (m.d 0 2) (by simp) with h10909 | h10909
                                    · linarith only [h10909, hlam, p10866_0]
                                    · rcases p10866_3 (m.d 1 2) (by simp) with h10911 | h10911
                                      · linarith only [h10698, h10911, hlam]
                                      · rcases p10866_3 (m.d 2 3) (by simp) with h10913 | h10913
                                        · rcases p10866_3 (m.d 2 4) (by simp) with h10914 | h10914
                                          · rcases p10866_3 (m.d 2 5) (by simp) with h10915 | h10915
                                            · rcases h3bigk with h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c | h10916c
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [hlam, p10916_0]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [h10694, h4, hc12, hc23, hlam, hphi, p10916_1]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [h4, hlam, p10916_1]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                rcases p10916_3 (m.d 0 3) (by simp) with h10920 | h10920
                                                · rcases p10916_3 (m.d 1 3) (by simp) with h10921 | h10921
                                                  · linarith only [h1, h10921, hlam]
                                                  · linarith only [h10700, h10921, hlam]
                                                · linarith only [h10920, hlam, p10916_0]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                rcases p10916_3 (m.d 0 3) (by simp) with h10925 | h10925
                                                · rcases p10916_3 (m.d 1 3) (by simp) with h10926 | h10926
                                                  · linarith only [h1, h10926, hlam]
                                                  · linarith only [h10701, h10926, hlam]
                                                · linarith only [h10925, hlam, p10916_0]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [h1, hlam, p10916_0]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [hlam, p10916_0]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [h10694, hlam, p10916_1]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10916_1]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [h1, h10707, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10916_1]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10709_1, p10916_1]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [h10694, hc12, hc23, hlam, hphi, p10916_1]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [hlam, p10916_0]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                rcases p10916_3 (m.d 0 3) (by simp) with h10938 | h10938
                                                · linarith only [h10938, h4, hlam]
                                                · linarith only [h10938, h9250, hlam]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                rcases p10916_3 (m.d 0 3) (by simp) with h10941 | h10941
                                                · linarith only [h10941, h4, hlam]
                                                · linarith only [h10941, h9251, hlam]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [h9250, hlam, p10916_0]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [h10700, hlam, p10916_0]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [h10704, hlam, p10916_0]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [hlam, p10916_0]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [h10707, hlam, p10916_1]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [h9251, hlam, p10916_0]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [h10701, hlam, p10916_0]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [h10705, hlam, p10916_0]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [h10701, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10916_1]
                                              · have p10916_0 := h10916c.1
                                                have p10916_1 := h10916c.2.1
                                                have p10916_2 := h10916c.2.2.1
                                                have p10916_3 := h10916c.2.2.2
                                                linarith only [hlam, p10916_0]
                                            · linarith only [h10915, hlam, p10866_0]
                                          · linarith only [h10914, h7337, hlam]
                                        · linarith only [h10913, h4, hlam]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    rcases p10866_3 (m.d 0 2) (by simp) with h10957 | h10957
                                    · linarith only [h10957, h8360, hlam]
                                    · linarith only [h0, h10957, hlam]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [h10705, hlam, p10866_1]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [h10706, hlam, p10866_0]
                                  · have p10866_0 := h10866c.1
                                    have p10866_1 := h10866c.2.1
                                    have p10866_2 := h10866c.2.2.1
                                    have p10866_3 := h10866c.2.2.2
                                    linarith only [hlam, p10866_0]
                            · linarith only [h10861, h9251, hlam]
                        · linarith only [h10858, h3, hlam]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [h2, hlam, p10709_0]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [h0, h9252, hc12, hc45, hlam, hphi, ht23, ht34, p10709_1]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [h9250, hlam, p10709_0]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [hlam, p10709_0]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [h9252, hlam, p10709_0]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [h3, hlam, p10709_0]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [h0, h10704, h10706, h9252, hc12, hc23, hlam, hphi, p10709_1]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [h9251, hlam, p10709_0]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [h10696, h10704, h10706, h2, h9252, hc12, hc23, hlam, hphi, p10709_1]
                      · have p10709_0 := h10709c.1
                        have p10709_1 := h10709c.2.1
                        have p10709_2 := h10709c.2.2.1
                        have p10709_3 := h10709c.2.2.2
                        linarith only [hlam, p10709_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h10975 | h10975
                    · linarith only [h0, h10706, h10975, h7337, hc12, hc34, hlam, hphi, ht23]
                    · rcases h0bigk with h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c | h10977c
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        linarith only [hlam, p10977_0]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        rcases p10977_3 (m.d 0 1) (by simp) with h10979 | h10979
                        · rcases p10977_3 (m.d 0 2) (by simp) with h10980 | h10980
                          · linarith only [h0, h10980, hlam]
                          · rcases p10977_3 (m.d 0 3) (by simp) with h10982 | h10982
                            · linarith only [h1, h10982, hlam]
                            · linarith only [h10982, h4, hlam]
                        · linarith only [h0, h10979, hlam]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        rcases p10977_3 (m.d 0 1) (by simp) with h10986 | h10986
                        · rcases p10977_3 (m.d 0 2) (by simp) with h10987 | h10987
                          · linarith only [h0, h10987, hlam]
                          · rcases p10977_3 (m.d 0 3) (by simp) with h10989 | h10989
                            · linarith only [h1, h10989, hlam]
                            · rcases p10977_3 (m.d 0 4) (by simp) with h10991 | h10991
                              · linarith only [h10991, h2, hlam]
                              · rcases p10977_3 (m.d 0 5) (by simp) with h10993 | h10993
                                · linarith only [h10993, h3, hlam]
                                · rcases h2bigk with h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c | h10995c
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [hlam, p10995_0]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [h7337, hc12, hc24, hlam, hphi, p10995_1]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [h4, hlam, p10995_0]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [h7337, hlam, p10995_0]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [h8360, hlam, p10995_0]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [h0, hlam, p10995_0]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [hlam, p10995_0]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [h10694, hlam, p10995_0]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [h10696, hlam, p10995_0]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [h10698, hlam, p10995_0]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    rcases p10995_3 (m.d 0 2) (by simp) with h11006 | h11006
                                    · linarith only [h11006, hlam, p10995_0]
                                    · rcases p10995_3 (m.d 1 2) (by simp) with h11008 | h11008
                                      · linarith only [h10694, h11008, hlam]
                                      · rcases p10995_3 (m.d 2 3) (by simp) with h11010 | h11010
                                        · rcases p10995_3 (m.d 2 4) (by simp) with h11011 | h11011
                                          · linarith only [h10704, h11011, hlam]
                                          · linarith only [h11011, h7337, hlam]
                                        · linarith only [h11010, hlam, p10995_0]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    rcases p10995_3 (m.d 0 2) (by simp) with h11015 | h11015
                                    · linarith only [h11015, h4, hlam]
                                    · linarith only [h0, h11015, hlam]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [hlam, p10995_0]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [h7337, hc02, hc23, hlam, hphi, p10995_1]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [h0, h8360, hc12, hc23, hlam, hphi, p10995_1]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [h0, h10706, hc12, hc45, hlam, hphi, ht23, ht34, p10995_1]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [h10706, hc12, hc45, hlam, hphi, ht23, ht34, p10995_1]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [h10704, hlam, p10995_1]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [hlam, p10995_0]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [h10706, hlam, p10995_1]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    rcases p10995_3 (m.d 0 2) (by simp) with h11026 | h11026
                                    · linarith only [h11026, hlam, p10995_0]
                                    · rcases p10995_3 (m.d 1 2) (by simp) with h11028 | h11028
                                      · linarith only [h10698, h11028, hlam]
                                      · rcases p10995_3 (m.d 2 3) (by simp) with h11030 | h11030
                                        · rcases p10995_3 (m.d 2 4) (by simp) with h11031 | h11031
                                          · linarith only [h10706, h11031, hlam]
                                          · linarith only [h11031, h7337, hlam]
                                        · linarith only [h11030, h4, hlam]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    rcases p10995_3 (m.d 0 2) (by simp) with h11035 | h11035
                                    · linarith only [h11035, h8360, hlam]
                                    · linarith only [h0, h11035, hlam]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [h10705, hlam, p10995_1]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [h0, h7337, hc12, hc25, hlam, hphi, p10995_1]
                                  · have p10995_0 := h10995c.1
                                    have p10995_1 := h10995c.2.1
                                    have p10995_2 := h10995c.2.2.1
                                    have p10995_3 := h10995c.2.2.2
                                    linarith only [hlam, p10995_0]
                        · linarith only [h1, h10986, hlam]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        rcases p10977_3 (m.d 0 1) (by simp) with h11042 | h11042
                        · rcases p10977_3 (m.d 0 2) (by simp) with h11043 | h11043
                          · linarith only [h0, h11043, hlam]
                          · rcases p10977_3 (m.d 0 3) (by simp) with h11045 | h11045
                            · linarith only [h1, h11045, hlam]
                            · linarith only [h11045, h9250, hlam]
                        · linarith only [h11042, h2, hlam]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        rcases p10977_3 (m.d 0 1) (by simp) with h11049 | h11049
                        · rcases p10977_3 (m.d 0 2) (by simp) with h11050 | h11050
                          · linarith only [h0, h11050, hlam]
                          · rcases p10977_3 (m.d 0 3) (by simp) with h11052 | h11052
                            · linarith only [h1, h11052, hlam]
                            · linarith only [h11052, h9251, hlam]
                        · linarith only [h11049, h3, hlam]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        linarith only [h0, hlam, p10977_0]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        linarith only [hlam, p10977_0]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        linarith only [h4, hlam, p10977_0]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        linarith only [h7337, hlam, p10977_1]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        linarith only [h8360, hlam, p10977_0]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        linarith only [h1, hlam, p10977_1]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        rcases p10977_3 (m.d 0 1) (by simp) with h11062 | h11062
                        · rcases p10977_3 (m.d 0 2) (by simp) with h11063 | h11063
                          · linarith only [h11063, h4, hlam]
                          · rcases p10977_3 (m.d 0 3) (by simp) with h11065 | h11065
                            · rcases p10977_3 (m.d 0 4) (by simp) with h11066 | h11066
                              · linarith only [h11066, h9250, hlam]
                              · linarith only [h11066, h7337, hlam]
                            · linarith only [h11065, h4, hlam]
                        · linarith only [h0, h11062, hlam]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        linarith only [hlam, p10977_0]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        rcases p10977_3 (m.d 0 1) (by simp) with h11072 | h11072
                        · rcases p10977_3 (m.d 0 2) (by simp) with h11073 | h11073
                          · linarith only [h11073, h4, hlam]
                          · rcases p10977_3 (m.d 0 3) (by simp) with h11075 | h11075
                            · rcases p10977_3 (m.d 0 4) (by simp) with h11076 | h11076
                              · linarith only [h11076, h9250, hlam]
                              · rcases p10977_3 (m.d 0 5) (by simp) with h11078 | h11078
                                · linarith only [h11078, h9251, hlam]
                                · linarith only [h11078, h9252, hlam]
                            · linarith only [h11075, h9250, hlam]
                        · linarith only [h11072, h2, hlam]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        rcases p10977_3 (m.d 0 1) (by simp) with h11083 | h11083
                        · rcases p10977_3 (m.d 0 2) (by simp) with h11084 | h11084
                          · linarith only [h11084, h4, hlam]
                          · rcases p10977_3 (m.d 0 3) (by simp) with h11086 | h11086
                            · rcases p10977_3 (m.d 0 4) (by simp) with h11087 | h11087
                              · linarith only [h11087, h9250, hlam]
                              · rcases p10977_3 (m.d 0 5) (by simp) with h11089 | h11089
                                · linarith only [h11089, h9251, hlam]
                                · rcases h2bigk with h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c | h11091c
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [hlam, p11091_0]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [h7337, hc12, hc24, hlam, hphi, p11091_1]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [h4, hlam, p11091_0]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [h7337, hlam, p11091_0]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [h8360, hlam, p11091_0]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [h0, hlam, p11091_0]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [hlam, p11091_0]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [h10694, hlam, p11091_0]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [h10696, hlam, p11091_0]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [h10698, hlam, p11091_0]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    rcases p11091_3 (m.d 0 2) (by simp) with h11102 | h11102
                                    · linarith only [h11102, hlam, p11091_0]
                                    · rcases p11091_3 (m.d 1 2) (by simp) with h11104 | h11104
                                      · linarith only [h10694, h11104, hlam]
                                      · rcases p11091_3 (m.d 2 3) (by simp) with h11106 | h11106
                                        · rcases p11091_3 (m.d 2 4) (by simp) with h11107 | h11107
                                          · linarith only [h10704, h11107, hlam]
                                          · linarith only [h11107, h7337, hlam]
                                        · linarith only [h11106, hlam, p11091_0]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    rcases p11091_3 (m.d 0 2) (by simp) with h11111 | h11111
                                    · linarith only [h11111, h4, hlam]
                                    · linarith only [h0, h11111, hlam]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [hlam, p11091_0]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [h7337, hc02, hc23, hlam, hphi, p11091_1]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [h0, h8360, hc12, hc23, hlam, hphi, p11091_1]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [h0, h10706, hc12, hc45, hlam, hphi, ht23, ht34, p11091_1]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [h10706, hc12, hc45, hlam, hphi, ht23, ht34, p11091_1]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [h10704, hlam, p11091_1]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [hlam, p11091_0]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [h10706, hlam, p11091_1]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    rcases p11091_3 (m.d 0 2) (by simp) with h11122 | h11122
                                    · linarith only [h11122, hlam, p11091_0]
                                    · rcases p11091_3 (m.d 1 2) (by simp) with h11124 | h11124
                                      · linarith only [h10698, h11124, hlam]
                                      · rcases p11091_3 (m.d 2 3) (by simp) with h11126 | h11126
                                        · rcases p11091_3 (m.d 2 4) (by simp) with h11127 | h11127
                                          · linarith only [h10706, h11127, hlam]
                                          · linarith only [h11127, h7337, hlam]
                                        · linarith only [h11126, h4, hlam]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    rcases p11091_3 (m.d 0 2) (by simp) with h11131 | h11131
                                    · linarith only [h11131, h8360, hlam]
                                    · linarith only [h0, h11131, hlam]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [h10705, hlam, p11091_1]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [h0, h7337, hc12, hc25, hlam, hphi, p11091_1]
                                  · have p11091_0 := h11091c.1
                                    have p11091_1 := h11091c.2.1
                                    have p11091_2 := h11091c.2.2.1
                                    have p11091_3 := h11091c.2.2.2
                                    linarith only [hlam, p11091_0]
                            · linarith only [h11086, h9251, hlam]
                        · linarith only [h11083, h3, hlam]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        linarith only [h2, hlam, p10977_0]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        linarith only [h0, h9252, hc12, hc45, hlam, hphi, ht23, ht34, p10977_1]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        linarith only [h9250, hlam, p10977_0]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        linarith only [hlam, p10977_0]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        linarith only [h9252, hlam, p10977_0]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        linarith only [h3, hlam, p10977_0]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        rcases p10977_3 (m.d 0 1) (by simp) with h11145 | h11145
                        · rcases p10977_3 (m.d 0 2) (by simp) with h11146 | h11146
                          · linarith only [h11146, h8360, hlam]
                          · rcases p10977_3 (m.d 0 3) (by simp) with h11148 | h11148
                            · rcases p10977_3 (m.d 0 4) (by simp) with h11149 | h11149
                              · linarith only [h11149, h9252, hlam]
                              · linarith only [h11149, h7337, hlam]
                            · linarith only [h11148, h4, hlam]
                        · linarith only [h0, h11145, hlam]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        linarith only [h9251, hlam, p10977_0]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        rcases p10977_3 (m.d 0 1) (by simp) with h11155 | h11155
                        · rcases p10977_3 (m.d 0 2) (by simp) with h11156 | h11156
                          · linarith only [h11156, h8360, hlam]
                          · rcases p10977_3 (m.d 0 3) (by simp) with h11158 | h11158
                            · rcases p10977_3 (m.d 0 4) (by simp) with h11159 | h11159
                              · linarith only [h11159, h9252, hlam]
                              · rcases p10977_3 (m.d 0 5) (by simp) with h11161 | h11161
                                · rcases h2bigk with h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c | h11162c
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [hlam, p11162_0]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [h4, hc12, hc23, hlam, hphi, p11162_1]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [h4, hlam, p11162_0]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [h7337, hlam, p11162_0]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [h8360, hlam, p11162_0]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [h0, hlam, p11162_0]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [hlam, p11162_0]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [h10694, hlam, p11162_0]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [h10696, hlam, p11162_0]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [h10698, hlam, p11162_0]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    rcases p11162_3 (m.d 0 2) (by simp) with h11173 | h11173
                                    · linarith only [h11173, hlam, p11162_0]
                                    · rcases p11162_3 (m.d 1 2) (by simp) with h11175 | h11175
                                      · linarith only [h10694, h11175, hlam]
                                      · rcases p11162_3 (m.d 2 3) (by simp) with h11177 | h11177
                                        · rcases p11162_3 (m.d 2 4) (by simp) with h11178 | h11178
                                          · linarith only [h10704, h11178, hlam]
                                          · linarith only [h11178, h7337, hlam]
                                        · linarith only [h11177, hlam, p11162_0]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    rcases p11162_3 (m.d 0 2) (by simp) with h11182 | h11182
                                    · linarith only [h11182, h4, hlam]
                                    · linarith only [h0, h11182, hlam]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [hlam, p11162_0]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [h7337, hc02, hc23, hlam, hphi, p11162_1]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [h0, h8360, hc12, hc23, hlam, hphi, p11162_1]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [h0, h10706, hc12, hc45, hlam, hphi, ht23, ht34, p11162_1]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [h10706, hc12, hc45, hlam, hphi, ht23, ht34, p11162_1]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [h10704, hlam, p11162_1]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [hlam, p11162_0]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [h10706, hlam, p11162_1]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    rcases p11162_3 (m.d 0 2) (by simp) with h11193 | h11193
                                    · linarith only [h11193, hlam, p11162_0]
                                    · rcases p11162_3 (m.d 1 2) (by simp) with h11195 | h11195
                                      · linarith only [h10698, h11195, hlam]
                                      · rcases p11162_3 (m.d 2 3) (by simp) with h11197 | h11197
                                        · rcases p11162_3 (m.d 2 4) (by simp) with h11198 | h11198
                                          · linarith only [h10706, h11198, hlam]
                                          · linarith only [h11198, h7337, hlam]
                                        · linarith only [h11197, h4, hlam]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    rcases p11162_3 (m.d 0 2) (by simp) with h11202 | h11202
                                    · linarith only [h11202, h8360, hlam]
                                    · linarith only [h0, h11202, hlam]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [h10705, hlam, p11162_1]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [h0, h7337, hc12, hc25, hlam, hphi, p11162_1]
                                  · have p11162_0 := h11162c.1
                                    have p11162_1 := h11162c.2.1
                                    have p11162_2 := h11162c.2.2.1
                                    have p11162_3 := h11162c.2.2.2
                                    linarith only [hlam, p11162_0]
                                · linarith only [h11161, h9252, hlam]
                            · linarith only [h11158, h9250, hlam]
                        · linarith only [h11155, h2, hlam]
                      · have p10977_0 := h10977c.1
                        have p10977_1 := h10977c.2.1
                        have p10977_2 := h10977c.2.2.1
                        have p10977_3 := h10977c.2.2.2
                        linarith only [hlam, p10977_0]
                · linarith only [h1, h10701, h10705, h4, hlam]
              · linarith only [h1, h10700, h10704, h4, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h11214 | h11214
            · linarith only [h10700, h10701, h11214, h7337, h9251, h9252, hc02, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h11216 | h11216
              · rcases m.htr 2 3 5 (by decide) (by decide) with h11217 | h11217
                · rcases m.htr 2 4 5 (by decide) (by decide) with h11218 | h11218
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11219 | h11219
                    · linarith only [h10700, h10701, h11219, h9251, h9252, hlam]
                    · rcases h0bigk with h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c | h11221c
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [hlam, p11221_0]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        rcases p11221_3 (m.d 0 1) (by simp) with h11223 | h11223
                        · rcases p11221_3 (m.d 0 2) (by simp) with h11224 | h11224
                          · linarith only [h0, h11224, hlam]
                          · rcases p11221_3 (m.d 0 3) (by simp) with h11226 | h11226
                            · linarith only [h1, h11226, hlam]
                            · linarith only [h11226, h4, hlam]
                        · linarith only [h0, h11223, hlam]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [h10700, h10701, h9251, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11221_1]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        rcases p11221_3 (m.d 0 1) (by simp) with h11231 | h11231
                        · rcases p11221_3 (m.d 0 2) (by simp) with h11232 | h11232
                          · linarith only [h0, h11232, hlam]
                          · rcases p11221_3 (m.d 0 3) (by simp) with h11234 | h11234
                            · linarith only [h1, h11234, hlam]
                            · linarith only [h11234, h9250, hlam]
                        · linarith only [h11231, h2, hlam]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [h10700, h10701, h9251, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11221_1]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [h0, hlam, p11221_0]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [hlam, p11221_0]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [h4, hlam, p11221_0]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [h7337, hlam, p11221_1]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [h8360, hlam, p11221_0]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [h1, hlam, p11221_1]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        rcases p11221_3 (m.d 0 1) (by simp) with h11245 | h11245
                        · rcases p11221_3 (m.d 0 2) (by simp) with h11246 | h11246
                          · linarith only [h11246, h4, hlam]
                          · rcases p11221_3 (m.d 0 3) (by simp) with h11248 | h11248
                            · rcases p11221_3 (m.d 0 4) (by simp) with h11249 | h11249
                              · linarith only [h11249, h9250, hlam]
                              · linarith only [h11249, h7337, hlam]
                            · linarith only [h11248, h4, hlam]
                        · linarith only [h0, h11245, hlam]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [hlam, p11221_0]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        rcases p11221_3 (m.d 0 1) (by simp) with h11255 | h11255
                        · rcases p11221_3 (m.d 0 2) (by simp) with h11256 | h11256
                          · linarith only [h11256, h4, hlam]
                          · rcases p11221_3 (m.d 0 3) (by simp) with h11258 | h11258
                            · rcases p11221_3 (m.d 0 4) (by simp) with h11259 | h11259
                              · linarith only [h11259, h9250, hlam]
                              · rcases p11221_3 (m.d 0 5) (by simp) with h11261 | h11261
                                · linarith only [h11261, h9251, hlam]
                                · linarith only [h11261, h9252, hlam]
                            · linarith only [h11258, h9250, hlam]
                        · linarith only [h11255, h2, hlam]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [h10700, h10701, h9251, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p11221_1]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [h2, hlam, p11221_0]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [h0, h9252, hc12, hc45, hlam, hphi, ht23, ht34, p11221_1]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [h9250, hlam, p11221_0]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [hlam, p11221_0]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [h9252, hlam, p11221_0]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [h3, hlam, p11221_0]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [h0, h11216, h11218, h9252, hc12, hc23, hlam, hphi, p11221_1]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [h9251, hlam, p11221_0]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [h0, h11216, h11218, h7337, h9252, hc12, hc23, hlam, hphi, p11221_1]
                      · have p11221_0 := h11221c.1
                        have p11221_1 := h11221c.2.1
                        have p11221_2 := h11221c.2.2.1
                        have p11221_3 := h11221c.2.2.2
                        linarith only [hlam, p11221_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11277 | h11277
                    · linarith only [h10700, h10701, h11218, h11277, h9251, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h0bigk with h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c | h11279c
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [hlam, p11279_0]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        rcases p11279_3 (m.d 0 1) (by simp) with h11281 | h11281
                        · rcases p11279_3 (m.d 0 2) (by simp) with h11282 | h11282
                          · linarith only [h0, h11282, hlam]
                          · rcases p11279_3 (m.d 0 3) (by simp) with h11284 | h11284
                            · linarith only [h1, h11284, hlam]
                            · linarith only [h11284, h4, hlam]
                        · linarith only [h0, h11281, hlam]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [h10701, h9251, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p11279_1]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        rcases p11279_3 (m.d 0 1) (by simp) with h11289 | h11289
                        · rcases p11279_3 (m.d 0 2) (by simp) with h11290 | h11290
                          · linarith only [h0, h11290, hlam]
                          · rcases p11279_3 (m.d 0 3) (by simp) with h11292 | h11292
                            · linarith only [h1, h11292, hlam]
                            · linarith only [h11292, h9250, hlam]
                        · linarith only [h11289, h2, hlam]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [h10700, h10701, h9251, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11279_1]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [h0, hlam, p11279_0]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [hlam, p11279_0]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [h4, hlam, p11279_0]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [h7337, hlam, p11279_1]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [h8360, hlam, p11279_0]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [h1, hlam, p11279_1]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        rcases p11279_3 (m.d 0 1) (by simp) with h11303 | h11303
                        · rcases p11279_3 (m.d 0 2) (by simp) with h11304 | h11304
                          · linarith only [h11304, h4, hlam]
                          · rcases p11279_3 (m.d 0 3) (by simp) with h11306 | h11306
                            · rcases p11279_3 (m.d 0 4) (by simp) with h11307 | h11307
                              · linarith only [h11307, h9250, hlam]
                              · linarith only [h11307, h7337, hlam]
                            · linarith only [h11306, h4, hlam]
                        · linarith only [h0, h11303, hlam]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [hlam, p11279_0]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        rcases p11279_3 (m.d 0 1) (by simp) with h11313 | h11313
                        · rcases p11279_3 (m.d 0 2) (by simp) with h11314 | h11314
                          · linarith only [h11314, h4, hlam]
                          · rcases p11279_3 (m.d 0 3) (by simp) with h11316 | h11316
                            · rcases p11279_3 (m.d 0 4) (by simp) with h11317 | h11317
                              · linarith only [h11317, h9250, hlam]
                              · rcases p11279_3 (m.d 0 5) (by simp) with h11319 | h11319
                                · linarith only [h11319, h9251, hlam]
                                · linarith only [h11319, h9252, hlam]
                            · linarith only [h11316, h9250, hlam]
                        · linarith only [h11313, h2, hlam]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [h10700, h10701, h9251, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p11279_1]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [h2, hlam, p11279_0]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [h0, h11218, h7337, hc12, hc45, hlam, hphi, ht23, ht34, p11279_1]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [h9250, hlam, p11279_0]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [hlam, p11279_0]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [h9252, hlam, p11279_0]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [h3, hlam, p11279_0]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        rcases p11279_3 (m.d 0 1) (by simp) with h11331 | h11331
                        · rcases p11279_3 (m.d 0 2) (by simp) with h11332 | h11332
                          · linarith only [h11332, h8360, hlam]
                          · rcases p11279_3 (m.d 0 3) (by simp) with h11334 | h11334
                            · rcases p11279_3 (m.d 0 4) (by simp) with h11335 | h11335
                              · linarith only [h11335, h9252, hlam]
                              · linarith only [h11335, h7337, hlam]
                            · linarith only [h11334, h4, hlam]
                        · linarith only [h0, h11331, hlam]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [h9251, hlam, p11279_0]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        rcases p11279_3 (m.d 0 1) (by simp) with h11341 | h11341
                        · rcases p11279_3 (m.d 0 2) (by simp) with h11342 | h11342
                          · linarith only [h11342, h8360, hlam]
                          · rcases p11279_3 (m.d 0 3) (by simp) with h11344 | h11344
                            · rcases p11279_3 (m.d 0 4) (by simp) with h11345 | h11345
                              · linarith only [h11345, h9252, hlam]
                              · rcases p11279_3 (m.d 0 5) (by simp) with h11347 | h11347
                                · rcases h2bigk with h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c | h11348c
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [hlam, p11348_0]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [h7337, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11279_1, p11348_1]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [h4, hlam, p11348_0]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [h7337, hlam, p11348_0]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [h8360, hlam, p11348_0]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [h0, hlam, p11348_0]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [hlam, p11348_0]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [h10694, hlam, p11348_0]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [h10696, hlam, p11348_0]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [h10698, hlam, p11348_0]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    rcases p11348_3 (m.d 0 2) (by simp) with h11359 | h11359
                                    · linarith only [h11359, hlam, p11348_0]
                                    · rcases p11348_3 (m.d 1 2) (by simp) with h11361 | h11361
                                      · linarith only [h10694, h11361, hlam]
                                      · rcases p11348_3 (m.d 2 3) (by simp) with h11363 | h11363
                                        · rcases p11348_3 (m.d 2 4) (by simp) with h11364 | h11364
                                          · linarith only [h11216, h11364, hlam]
                                          · linarith only [h11364, h7337, hlam]
                                        · linarith only [h11363, hlam, p11348_0]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    rcases p11348_3 (m.d 0 2) (by simp) with h11368 | h11368
                                    · linarith only [h11368, h4, hlam]
                                    · linarith only [h0, h11368, hlam]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [hlam, p11348_0]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [h7337, hc02, hc23, hlam, hphi, p11348_1]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [h8360, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11279_1, p11348_1]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [h0, h11218, hc12, hc45, hlam, hphi, ht23, ht34, p11348_1]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [h11218, hc12, hc45, hlam, hphi, ht23, ht34, p11348_1]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [h11216, hlam, p11348_1]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [hlam, p11348_0]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [h11218, hlam, p11348_1]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    rcases p11348_3 (m.d 0 2) (by simp) with h11379 | h11379
                                    · linarith only [h11379, hlam, p11348_0]
                                    · rcases p11348_3 (m.d 1 2) (by simp) with h11381 | h11381
                                      · linarith only [h10698, h11381, hlam]
                                      · rcases p11348_3 (m.d 2 3) (by simp) with h11383 | h11383
                                        · rcases p11348_3 (m.d 2 4) (by simp) with h11384 | h11384
                                          · linarith only [h11218, h11384, hlam]
                                          · linarith only [h11384, h7337, hlam]
                                        · linarith only [h11383, h4, hlam]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    rcases p11348_3 (m.d 0 2) (by simp) with h11388 | h11388
                                    · linarith only [h11388, h8360, hlam]
                                    · linarith only [h0, h11388, hlam]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [h11217, hlam, p11348_1]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [h0, h7337, hc12, hc25, hlam, hphi, p11348_1]
                                  · have p11348_0 := h11348c.1
                                    have p11348_1 := h11348c.2.1
                                    have p11348_2 := h11348c.2.2.1
                                    have p11348_3 := h11348c.2.2.2
                                    linarith only [hlam, p11348_0]
                                · linarith only [h11347, h9252, hlam]
                            · linarith only [h11344, h9250, hlam]
                        · linarith only [h11341, h2, hlam]
                      · have p11279_0 := h11279c.1
                        have p11279_1 := h11279c.2.1
                        have p11279_2 := h11279c.2.2.1
                        have p11279_3 := h11279c.2.2.2
                        linarith only [hlam, p11279_0]
                · linarith only [h11217, h4, h9251, hlam]
              · linarith only [h10700, h10701, h11216, h4, h9251, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h11400 | h11400
          · rcases m.htr 1 4 5 (by decide) (by decide) with h11401 | h11401
            · linarith only [h10700, h11400, h11401, h9250, h9252, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h10700, h11400, h11401, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h11404 | h11404
            · linarith only [h11404, h2, h9252, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h11406 | h11406
              · rcases m.htr 2 3 5 (by decide) (by decide) with h11407 | h11407
                · rcases m.htr 2 4 5 (by decide) (by decide) with h11408 | h11408
                  · linarith only [h10694, h10700, h11408, h9250, h9252, hc12, hc24, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11410 | h11410
                    · linarith only [h11408, h11410, h7337, h9250, hlam]
                    · rcases h0bigk with h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c | h11412c
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [hlam, p11412_0]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        rcases p11412_3 (m.d 0 1) (by simp) with h11414 | h11414
                        · rcases p11412_3 (m.d 0 2) (by simp) with h11415 | h11415
                          · linarith only [h0, h11415, hlam]
                          · rcases p11412_3 (m.d 0 3) (by simp) with h11417 | h11417
                            · linarith only [h1, h11417, hlam]
                            · linarith only [h11417, h4, hlam]
                        · linarith only [h0, h11414, hlam]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [h10694, h10700, h9250, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11412_1]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        rcases p11412_3 (m.d 0 1) (by simp) with h11422 | h11422
                        · rcases p11412_3 (m.d 0 2) (by simp) with h11423 | h11423
                          · linarith only [h0, h11423, hlam]
                          · rcases p11412_3 (m.d 0 3) (by simp) with h11425 | h11425
                            · linarith only [h1, h11425, hlam]
                            · linarith only [h11425, h9250, hlam]
                        · linarith only [h11422, h2, hlam]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        rcases p11412_3 (m.d 0 1) (by simp) with h11429 | h11429
                        · rcases p11412_3 (m.d 0 2) (by simp) with h11430 | h11430
                          · linarith only [h0, h11430, hlam]
                          · rcases p11412_3 (m.d 0 3) (by simp) with h11432 | h11432
                            · linarith only [h1, h11432, hlam]
                            · linarith only [h11432, h9251, hlam]
                        · linarith only [h11429, h3, hlam]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [h0, hlam, p11412_0]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [hlam, p11412_0]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [h4, hlam, p11412_0]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [h7337, hlam, p11412_1]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [h8360, hlam, p11412_0]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [h1, hlam, p11412_1]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        rcases p11412_3 (m.d 0 1) (by simp) with h11442 | h11442
                        · rcases p11412_3 (m.d 0 2) (by simp) with h11443 | h11443
                          · linarith only [h11443, h4, hlam]
                          · rcases p11412_3 (m.d 0 3) (by simp) with h11445 | h11445
                            · rcases p11412_3 (m.d 0 4) (by simp) with h11446 | h11446
                              · linarith only [h11446, h9250, hlam]
                              · linarith only [h11446, h7337, hlam]
                            · linarith only [h11445, h4, hlam]
                        · linarith only [h0, h11442, hlam]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [hlam, p11412_0]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [h10694, h10700, h4, h9250, hc12, hc23, hlam, hphi, p11412_1]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [h10694, h10700, h11410, h4, h9251, hc12, hc23, hlam, hphi, p11412_1]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [h2, hlam, p11412_0]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [h0, h11408, h7337, hc12, hc45, hlam, hphi, ht23, ht34, p11412_1]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [h9250, hlam, p11412_0]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [hlam, p11412_0]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [h9252, hlam, p11412_0]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [h3, hlam, p11412_0]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        rcases p11412_3 (m.d 0 1) (by simp) with h11460 | h11460
                        · rcases p11412_3 (m.d 0 2) (by simp) with h11461 | h11461
                          · linarith only [h11461, h8360, hlam]
                          · rcases p11412_3 (m.d 0 3) (by simp) with h11463 | h11463
                            · rcases p11412_3 (m.d 0 4) (by simp) with h11464 | h11464
                              · linarith only [h11464, h9252, hlam]
                              · linarith only [h11464, h7337, hlam]
                            · linarith only [h11463, h4, hlam]
                        · linarith only [h0, h11460, hlam]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [h9251, hlam, p11412_0]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [h10694, h10700, h11408, h8360, h9250, hc12, hc45, hlam, hphi, ht23, ht34, p11412_1]
                      · have p11412_0 := h11412c.1
                        have p11412_1 := h11412c.2.1
                        have p11412_2 := h11412c.2.2.1
                        have p11412_3 := h11412c.2.2.2
                        linarith only [hlam, p11412_0]
                · linarith only [h10694, h10700, h11407, h4, h9250, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h11406, h4, h9250, hlam]

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s13_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9250 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9251 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  have h9250 := hg9250
  rcases m.htr 0 4 5 (by decide) (by decide) with h9252 | h9252
  · exact r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 hg9250 h9251 h9252
  · exact r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 hg9250 h9251 h9252

end R2N4
