import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_34S5
import Jsp000404.R1LeavesN7_34S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8838000 in
set_option maxHeartbeats 8838000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h763 | h763
  · rcases m.htr 0 4 5 (by decide) (by decide) with h764 | h764
    · rcases m.htr 1 2 3 (by decide) (by decide) with h765 | h765
      · rcases m.htr 1 2 4 (by decide) (by decide) with h766 | h766
        · rcases m.htr 1 3 4 (by decide) (by decide) with h767 | h767
          · linarith only [h1, h6, h763, h767, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h769 | h769
            · rcases m.htr 1 4 5 (by decide) (by decide) with h770 | h770
              · rcases m.htr 2 3 4 (by decide) (by decide) with h771 | h771
                · linarith only [h1, h6, h765, h771, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h773 | h773
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h774 | h774
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h775 | h775
                      · rcases h0bigk with h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [hlam, p776_0]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [h0, h766, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p776_1, u2ehi3]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          rcases p776_3 (m.d 0 1) (by simp) with h779 | h779
                          · rcases p776_3 (m.d 0 2) (by simp) with h780 | h780
                            · linarith only [h0, h780, hlam]
                            · linarith only [h3, h780, hlam]
                          · linarith only [h1, h779, hlam]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          rcases p776_3 (m.d 0 1) (by simp) with h784 | h784
                          · rcases p776_3 (m.d 0 2) (by simp) with h785 | h785
                            · linarith only [h0, h785, hlam]
                            · linarith only [h4, h785, hlam]
                          · linarith only [h784, hlam, p776_0]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          rcases p776_3 (m.d 0 1) (by simp) with h789 | h789
                          · rcases p776_3 (m.d 0 2) (by simp) with h790 | h790
                            · linarith only [h0, h790, hlam]
                            · linarith only [h5, h790, hlam]
                          · linarith only [h2, h789, hlam]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [h0, hlam, p776_0]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [hlam, p776_0]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          rcases p776_3 (m.d 0 1) (by simp) with h796 | h796
                          · rcases p776_3 (m.d 0 2) (by simp) with h797 | h797
                            · rcases p776_3 (m.d 0 3) (by simp) with h798 | h798
                              · linarith only [h3, h798, hlam]
                              · rcases p776_3 (m.d 0 4) (by simp) with h800 | h800
                                · linarith only [h4, h800, hlam]
                                · linarith only [h6, h800, hlam]
                            · linarith only [h3, h797, hlam]
                          · linarith only [h1, h796, hlam]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          rcases p776_3 (m.d 0 1) (by simp) with h805 | h805
                          · rcases p776_3 (m.d 0 2) (by simp) with h806 | h806
                            · rcases p776_3 (m.d 0 3) (by simp) with h807 | h807
                              · linarith only [h3, h807, hlam]
                              · rcases p776_3 (m.d 0 4) (by simp) with h809 | h809
                                · linarith only [h4, h809, hlam]
                                · rcases p776_3 (m.d 0 5) (by simp) with h811 | h811
                                  · linarith only [h5, h811, hlam]
                                  · rcases h3bigk with h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c | h813c
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [hlam, p813_0]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [h6, h765, h773, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p776_1, p813_1, u2ehi4]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [h0, h6, h773, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p776_1, p813_1, u2ehi4]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [h6, hlam, p813_0]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [h0, h6, h775, hc01, hc45, hlam, hphi, ht0b, ht5b, p776_1, p813_1]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [h1, hlam, p813_0]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [hlam, p813_0]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [h773, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p813_1, u2ehi4]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [h767, hlam, p813_0]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [h0, h1, h6, h775, hc01, hc45, hlam, hphi, ht0b, ht5b, p776_1, p813_1]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [h3, hlam, p813_0]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [h765, hlam, p813_0]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [hlam, p813_0]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [h771, hlam, p813_0]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [h766, h771, h775, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p813_1]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [hc03, hc34, hlam, hphi, p813_1]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [h765, hc34, hlam, hphi, ht23, p813_1, u2ehi2]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [hc34, hlam, hphi, ht23, p813_1, u2ehi2]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [hlam, p813_0]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      rcases p813_3 (m.d 0 3) (by simp) with h833 | h833
                                      · linarith only [h6, h833, hlam]
                                      · linarith only [h763, h833, hlam]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [h763, hlam, p813_0]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [h769, hlam, p813_0]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [h773, hlam, p813_0]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [h775, hlam, p813_0]
                                    · have p813_0 := h813c.1
                                      have p813_1 := h813c.2.1
                                      have p813_2 := h813c.2.2.1
                                      have p813_3 := h813c.2.2.2
                                      linarith only [hlam, p813_0]
                            · linarith only [h4, h806, hlam]
                          · linarith only [h0, h805, hlam, p776_1]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          rcases p776_3 (m.d 0 1) (by simp) with h843 | h843
                          · rcases p776_3 (m.d 0 2) (by simp) with h844 | h844
                            · rcases p776_3 (m.d 0 3) (by simp) with h845 | h845
                              · linarith only [h3, h845, hlam]
                              · linarith only [h763, h845, hlam]
                            · linarith only [h5, h844, hlam]
                          · linarith only [h2, h843, hlam]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [h1, hlam, p776_1]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [h3, hlam, p776_1]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [hlam, p776_0]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [h6, hlam, p776_1]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [h5, h6, hc34, hlam, hphi, ht23, p776_1, u2ehi4]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p776_1, u2ehi1]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [h4, hlam, p776_0]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [h3, h6, hc34, hlam, hphi, ht23, p776_1, u2ehi2]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [hlam, p776_0]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [h5, h6, hc34, hlam, hphi, ht23, p776_1, u2ehi4]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [h2, hlam, p776_0]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [h5, hlam, p776_1]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [h763, hlam, p776_0]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [h764, hlam, p776_1]
                        · have p776_0 := h776c.1
                          have p776_1 := h776c.2.1
                          have p776_2 := h776c.2.2.1
                          have p776_3 := h776c.2.2.2
                          linarith only [hlam, p776_0]
                      · linarith only [h1, h6, h765, h773, h775, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                    · linarith only [h2, h6, h763, h770, h771, h773, h774, hc34, hlam, hphi, ht23, u2ehi4]
                  · linarith only [h6, h763, h773, hc23, hc34, hlam, hphi]
              · linarith only [h6, h764, h766, h770, hc34, hlam, hphi, ht23, u2ehi3]
            · linarith only [h6, h763, h769, hc13, hc34, hlam, hphi]
        · linarith only [h765, h766, hc24, hlam, hphi, u2ehi2]
      · linarith only [h3, h6, h765, hc34, hlam, hphi, ht23, u2ehi1]
    · linarith only [h6, h763, h764, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h873 | h873
    · rcases m.htr 1 2 3 (by decide) (by decide) with h874 | h874
      · rcases m.htr 1 2 4 (by decide) (by decide) with h875 | h875
        · rcases m.htr 1 3 4 (by decide) (by decide) with h876 | h876
          · linarith only [h1, h6, h876, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h878 | h878
            · linarith only [h1, h763, h878, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h880 | h880
              · rcases m.htr 2 3 4 (by decide) (by decide) with h881 | h881
                · linarith only [h1, h6, h874, h881, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h883 | h883
                  · linarith only [h1, h763, h874, h883, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h885 | h885
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h886 | h886
                      · rcases h0bigk with h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [hlam, p887_0]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [h0, h875, h885, hc01, hc45, hlam, hphi, ht0b, ht5b, p887_1]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          rcases p887_3 (m.d 0 1) (by simp) with h890 | h890
                          · rcases p887_3 (m.d 0 2) (by simp) with h891 | h891
                            · linarith only [h0, h891, hlam]
                            · linarith only [h3, h891, hlam]
                          · linarith only [h1, h890, hlam]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          rcases p887_3 (m.d 0 1) (by simp) with h895 | h895
                          · rcases p887_3 (m.d 0 2) (by simp) with h896 | h896
                            · linarith only [h0, h896, hlam]
                            · linarith only [h4, h896, hlam]
                          · linarith only [h895, hlam, p887_0]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          rcases p887_3 (m.d 0 1) (by simp) with h900 | h900
                          · rcases p887_3 (m.d 0 2) (by simp) with h901 | h901
                            · linarith only [h0, h901, hlam]
                            · linarith only [h5, h901, hlam]
                          · linarith only [h2, h900, hlam]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [h0, hlam, p887_0]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [hlam, p887_0]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          rcases p887_3 (m.d 0 1) (by simp) with h907 | h907
                          · rcases p887_3 (m.d 0 2) (by simp) with h908 | h908
                            · rcases p887_3 (m.d 0 3) (by simp) with h909 | h909
                              · linarith only [h3, h909, hlam]
                              · rcases p887_3 (m.d 0 4) (by simp) with h911 | h911
                                · linarith only [h4, h911, hlam]
                                · linarith only [h6, h911, hlam]
                            · linarith only [h3, h908, hlam]
                          · linarith only [h1, h907, hlam]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          rcases p887_3 (m.d 0 1) (by simp) with h916 | h916
                          · rcases p887_3 (m.d 0 2) (by simp) with h917 | h917
                            · rcases p887_3 (m.d 0 3) (by simp) with h918 | h918
                              · linarith only [h3, h918, hlam]
                              · rcases p887_3 (m.d 0 4) (by simp) with h920 | h920
                                · linarith only [h4, h920, hlam]
                                · rcases p887_3 (m.d 0 5) (by simp) with h922 | h922
                                  · linarith only [h5, h922, hlam]
                                  · rcases h3bigk with h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [hlam, p924_0]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [h0, h763, h873, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p887_1, p924_1]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [h0, h763, h873, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p887_1, p924_1, u2ehi2]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [h6, hlam, p924_0]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [h763, hlam, p924_0]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [h1, hlam, p924_0]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [hlam, p924_0]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p924_1, u2ehi2]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [h876, hlam, p924_0]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [h878, hlam, p924_0]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [h3, hlam, p924_0]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [h874, hlam, p924_0]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [hlam, p924_0]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [h881, hlam, p924_0]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [h883, hlam, p924_0]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [hc03, hc34, hlam, hphi, p924_1]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [h874, hc34, hlam, hphi, ht23, p924_1, u2ehi2]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [hc34, hlam, hphi, ht23, p924_1, u2ehi2]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [hlam, p924_0]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [h1, h763, h874, hc34, hlam, hphi, ht23, p924_1, u2ehi2]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [h1, h874, hc35, hlam, hphi, ht23, p924_1, u2ehi2]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [h874, hc35, hlam, hphi, ht23, p924_1, u2ehi2]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht23, p924_1, u2ehi2]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [h886, hlam, p924_0]
                                    · have p924_0 := h924c.1
                                      have p924_1 := h924c.2.1
                                      have p924_2 := h924c.2.2.1
                                      have p924_3 := h924c.2.2.2
                                      linarith only [hlam, p924_0]
                            · linarith only [h4, h917, hlam]
                          · linarith only [h0, h916, hlam, p887_1]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          rcases p887_3 (m.d 0 1) (by simp) with h952 | h952
                          · rcases p887_3 (m.d 0 2) (by simp) with h953 | h953
                            · rcases p887_3 (m.d 0 3) (by simp) with h954 | h954
                              · linarith only [h3, h954, hlam]
                              · rcases p887_3 (m.d 0 4) (by simp) with h956 | h956
                                · linarith only [h4, h956, hlam]
                                · linarith only [h873, h956, hlam]
                            · linarith only [h5, h953, hlam]
                          · linarith only [h2, h952, hlam]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [h1, hlam, p887_1]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [h3, hlam, p887_1]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [hlam, p887_0]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [h6, hlam, p887_1]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [h763, hlam, p887_1]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [h0, h875, h883, h885, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p887_1, u2ehi2]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [h4, hlam, p887_0]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [h1, h6, h874, hc34, hlam, hphi, ht23, p887_1, u2ehi2]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [hlam, p887_0]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [h5, h6, h883, hc34, hlam, hphi, ht23, p887_1, u2ehi2]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [h2, hlam, p887_0]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [h5, hlam, p887_1]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [h1, h763, h874, h886, hc34, hlam, hphi, ht23, p887_1, u2ehi2]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [h873, hlam, p887_1]
                        · have p887_0 := h887c.1
                          have p887_1 := h887c.2.1
                          have p887_2 := h887c.2.2.1
                          have p887_3 := h887c.2.2.2
                          linarith only [hlam, p887_0]
                      · linarith only [h1, h6, h874, h886, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h6, h873, h885, hc34, hlam, hphi, ht23, u2ehi3]
              · linarith only [h6, h873, h875, h880, hc34, hlam, hphi, ht23, u2ehi3]
        · linarith only [h0, h4, h874, h875, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
      · linarith only [h3, h6, h874, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h981 | h981
      · rcases m.htr 1 2 4 (by decide) (by decide) with h982 | h982
        · rcases m.htr 1 3 4 (by decide) (by decide) with h983 | h983
          · linarith only [h1, h6, h983, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h985 | h985
            · linarith only [h1, h763, h985, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h987 | h987
              · linarith only [h0, h1, h6, h873, h981, h982, h987, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h989 | h989
                · linarith only [h1, h6, h981, h989, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h991 | h991
                  · linarith only [h1, h763, h981, h991, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h993 | h993
                    · linarith only [h4, h873, h993, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h995 | h995
                      · linarith only [h1, h6, h873, h981, h995, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h1, h6, h981, h995, hc45, hlam, hphi, ht23, ht34, u2ehi2]
        · linarith only [h4, h873, h982, hc45, hlam, hphi, ht23, ht34, u2ehi1]
      · linarith only [h3, h6, h981, hc34, hlam, hphi, ht23, u2ehi1]

set_option maxHeartbeats 8838000 in
set_option maxHeartbeats 8838000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
  · exact r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 h0 h1 h2 h3 h4 h5 h6
  · exact r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 h0 h1 h2 h3 h4 h5 h6

set_option maxHeartbeats 8838000 in
set_option maxHeartbeats 8838000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  linarith only [h3, h5, hc25, hlam, hphi, u2ehi2]

set_option maxHeartbeats 8838000 in
set_option maxHeartbeats 8838000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
  · exact r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 h0 h1 h2 h3 h4 h5
  · exact r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 h0 h1 h2 h3 h4 h5

set_option maxHeartbeats 8838000 in
set_option maxHeartbeats 8838000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]

set_option maxHeartbeats 8838000 in
set_option maxHeartbeats 8838000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · exact r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0_x0_x0 m hb0 hb2 hb3 h0 h1 h2 h3 h4
  · exact r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0_x0_x1 m hb0 hb2 hb3 h0 h1 h2 h3 h4

set_option maxHeartbeats 8838000 in
set_option maxHeartbeats 8838000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1002 | h1002
  · linarith only [h1002, h3, hc23, hlam, hphi, u2ehi3]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1004 | h1004
    · linarith only [h1004, h3, hc23, hlam, hphi, u2ehi4]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1006 | h1006
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1007 | h1007
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1008 | h1008
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1009 | h1009
            · linarith only [h0, h1002, h1009, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1011 | h1011
              · linarith only [h0, h1002, h1011, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1013 | h1013
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1014 | h1014
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1015 | h1015
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1016 | h1016
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1017 | h1017
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1018 | h1018
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1019 | h1019
                            · rcases h0bigk with h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [hlam, p1020_0]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                rcases p1020_3 (m.d 0 1) (by simp) with h1022 | h1022
                                · rcases p1020_3 (m.d 0 2) (by simp) with h1023 | h1023
                                  · linarith only [h0, h1023, hlam]
                                  · rcases p1020_3 (m.d 0 3) (by simp) with h1025 | h1025
                                    · linarith only [h1, h1025, hlam]
                                    · linarith only [h1025, h3, hlam]
                                · linarith only [h0, h1022, hlam]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [h1, h1013, h1019, hc01, hc45, hlam, hphi, ht0b, ht5b, p1020_1]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                rcases p1020_3 (m.d 0 1) (by simp) with h1030 | h1030
                                · rcases p1020_3 (m.d 0 2) (by simp) with h1031 | h1031
                                  · linarith only [h0, h1031, hlam]
                                  · rcases p1020_3 (m.d 0 3) (by simp) with h1033 | h1033
                                    · linarith only [h1, h1033, hlam]
                                    · linarith only [h1006, h1033, hlam]
                                · linarith only [h1030, hlam, p1020_0]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                rcases p1020_3 (m.d 0 1) (by simp) with h1037 | h1037
                                · rcases p1020_3 (m.d 0 2) (by simp) with h1038 | h1038
                                  · linarith only [h0, h1038, hlam]
                                  · rcases p1020_3 (m.d 0 3) (by simp) with h1040 | h1040
                                    · linarith only [h1, h1040, hlam]
                                    · linarith only [h1007, h1040, hlam]
                                · linarith only [h1037, h2, hlam]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [h0, hlam, p1020_0]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [hlam, p1020_0]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [h3, hlam, p1020_0]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [h1002, hlam, p1020_1]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [h1004, hlam, p1020_0]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [h1, hlam, p1020_1]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [h3, hc23, hlam, hphi, p1020_1, u2ehi0]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [hlam, p1020_0]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [h0, h1004, h1008, h3, hc23, hlam, hphi, p1020_1, u2ehi1]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [h0, h1004, h3, hc23, hlam, hphi, p1020_1, u2ehi1]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1020_1, u2ehi1]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [h0, h1002, h1016, hc23, hlam, hphi, p1020_1, u2ehi1]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [h1006, hlam, p1020_0]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [hlam, p1020_0]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [h0, h1002, h1004, h1016, hc23, hlam, hphi, p1020_1, u2ehi1]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [h2, hlam, p1020_0]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [h0, h1004, h1016, h1018, hc23, hlam, hphi, p1020_1, u2ehi1]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [h1007, hlam, p1020_0]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [h1008, hlam, p1020_1]
                              · have p1020_0 := h1020c.1
                                have p1020_1 := h1020c.2.1
                                have p1020_2 := h1020c.2.2.1
                                have p1020_3 := h1020c.2.2.2
                                linarith only [hlam, p1020_0]
                            · rcases h0bigk with h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                rcases p1064_3 (m.d 0 1) (by simp) with h1066 | h1066
                                · rcases p1064_3 (m.d 0 2) (by simp) with h1067 | h1067
                                  · linarith only [h0, h1067, hlam]
                                  · rcases p1064_3 (m.d 0 3) (by simp) with h1069 | h1069
                                    · linarith only [h1, h1069, hlam]
                                    · linarith only [h1069, h3, hlam]
                                · linarith only [h0, h1066, hlam]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1006, h1008, h1019, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1064_1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1008, h1019, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1064_1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                rcases p1064_3 (m.d 0 1) (by simp) with h1075 | h1075
                                · rcases p1064_3 (m.d 0 2) (by simp) with h1076 | h1076
                                  · linarith only [h0, h1076, hlam]
                                  · rcases p1064_3 (m.d 0 3) (by simp) with h1078 | h1078
                                    · linarith only [h1, h1078, hlam]
                                    · linarith only [h1007, h1078, hlam]
                                · linarith only [h1075, h2, hlam]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h0, hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h3, hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1002, hlam, p1064_1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1004, hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1, hlam, p1064_1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h0, h3, hc23, hlam, hphi, p1064_1, u2ehi1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1008, h1019, h3, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1064_1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h0, h1004, h3, hc23, hlam, hphi, p1064_1, u2ehi1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1064_1, u2ehi1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h0, h1002, h1016, hc23, hlam, hphi, p1064_1, u2ehi1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1006, hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h0, h1002, h1004, h1016, hc23, hlam, hphi, p1064_1, u2ehi1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h2, hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h0, h1004, h1016, h1018, hc23, hlam, hphi, p1064_1, u2ehi1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1007, hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1008, hlam, p1064_1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [hlam, p1064_0]
                          · linarith only [h1, h1013, h1015, h1018, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h0, h1017, h3, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h0, h1016, h3, hc34, hlam, hphi, ht23, u2ehi1]
                    · linarith only [h1002, h1008, h1011, h1015, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h1007, h1009, h1014, h3, hc23, hlam, hphi, u2ehi1]
                · linarith only [h1006, h1009, h1013, h3, hc23, hlam, hphi, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1108 | h1108
            · linarith only [h0, h1002, h1008, h1108, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1110 | h1110
              · linarith only [h0, h1002, h1008, h1110, hc45, hlam, hphi, ht23, ht34, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1112 | h1112
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1113 | h1113
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1114 | h1114
                    · linarith only [h1002, h1008, h1110, h1114, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1116 | h1116
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1117 | h1117
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1118 | h1118
                          · linarith only [h0, h1002, h1008, h1116, h1118, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h0, h1002, h1118, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                        · linarith only [h1, h1113, h1117, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h1112, h1114, h1116, h2, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h1007, h1108, h1113, h3, hc23, hlam, hphi, u2ehi1]
                · linarith only [h1006, h1108, h1112, h3, hc23, hlam, hphi, u2ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1125 | h1125
          · linarith only [h1006, h1007, h1125, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1127 | h1127
            · linarith only [h0, h1002, h1125, h1127, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1129 | h1129
              · linarith only [h0, h1002, h1125, h1129, hc45, hlam, hphi, ht23, ht34, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1131 | h1131
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1132 | h1132
                  · linarith only [h1, h1002, h1006, h1007, h1132, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1134 | h1134
                    · linarith only [h0, h1002, h1125, h1129, h1134, hc24, hlam, hphi, u2ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1136 | h1136
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1137 | h1137
                        · linarith only [h0, h1002, h1006, h1007, h1137, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h1137, h3, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h0, h1, h1131, h1136, h3, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                · linarith only [h1006, h1007, h1131, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1142 | h1142
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1143 | h1143
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1144 | h1144
            · linarith only [h0, h1002, h1144, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1146 | h1146
              · linarith only [h0, h1146, h3, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1148 | h1148
                · linarith only [h1, h1004, h1006, h1142, h1148, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1150 | h1150
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1151 | h1151
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1152 | h1152
                      · linarith only [h0, h1004, h1006, h1142, h1152, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h0, h1152, h3, hc34, hlam, hphi, ht23, u2ehi1]
                    · linarith only [h1002, h1143, h1146, h1151, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h1006, h1142, h1150, hc13, hc34, hlam, hphi]
          · linarith only [h1006, h1142, h1143, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1158 | h1158
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1159 | h1159
            · linarith only [h0, h1159, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1161 | h1161
              · linarith only [h0, h1161, h3, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1163 | h1163
                · linarith only [h1, h1006, h1163, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1165 | h1165
                  · linarith only [h1, h1142, h1165, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1167 | h1167
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1168 | h1168
                      · linarith only [h1, h1006, h1159, h1168, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h1168, h3, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1006, h1158, h1161, h1167, hc34, hlam, hphi, ht23, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1172 | h1172
            · linarith only [h0, h1172, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1174 | h1174
              · linarith only [h0, h1174, h3, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1176 | h1176
                · linarith only [h1, h1006, h1176, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1178 | h1178
                  · linarith only [h1, h1142, h1178, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1180 | h1180
                    · linarith only [h0, h1006, h1158, h1174, h1180, h3, hc24, hlam, hphi, u2ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1182 | h1182
                      · linarith only [h0, h1006, h1182, h3, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h0, h1182, h3, hc34, hlam, hphi, ht23, u2ehi1]

set_option maxHeartbeats 8838000 in
set_option maxHeartbeats 8838000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0_x0 m hb0 hb2 hb3 h0 h1 h2 h3
  · exact r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0_x1 m hb0 hb2 hb3 h0 h1 h2 h3

set_option maxHeartbeats 8838000 in
set_option maxHeartbeats 8838000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1185 | h1185
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1186 | h1186
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1187 | h1187
      · linarith only [h0, h1187, h2, hlam]
      · linarith only [h1186, h1187, hc25, hlam, hphi, u2ehi3]
    · linarith only [h1185, h1186, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1191 | h1191
    · linarith only [h1185, h1191, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1193 | h1193
      · linarith only [h1185, h1193, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1195 | h1195
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1196 | h1196
          · linarith only [h1, h1196, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1198 | h1198
            · linarith only [h0, h1195, h1196, h1198, h2, hc35, hlam, hphi, ht23, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1200 | h1200
              · linarith only [h0, h1191, h1195, h1196, h1200, hc35, hlam, hphi, ht23, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1202 | h1202
                · linarith only [h0, h1191, h1202, h2, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1204 | h1204
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1205 | h1205
                    · linarith only [h1, h1196, h1205, h2, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h1205, h2, hc35, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h1, h1195, h1200, h1204, h2, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1209 | h1209
          · linarith only [h0, h1195, h1209, h2, hc34, hlam, hphi, ht23, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1211 | h1211
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1212 | h1212
              · linarith only [h0, h1185, h1212, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1214 | h1214
                · linarith only [h1, h1191, h1211, h1212, h1214, h2, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1216 | h1216
                  · linarith only [h1, h1195, h1216, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1218 | h1218
                    · linarith only [h1, h1209, h1218, h2, hlam]
                    · linarith only [h1, h1212, h1218, h2, hc35, hlam, hphi, ht23, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1221 | h1221
              · linarith only [h0, h1185, h1221, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1223 | h1223
                · linarith only [h1, h1221, h1223, h2, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1225 | h1225
                  · linarith only [h0, h1, h1185, h1195, h1225, h2, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1227 | h1227
                    · linarith only [h1, h1209, h1227, hlam]
                    · linarith only [h0, h1227, h2, hc35, hlam, hphi, ht23, u2ehi1]

set_option maxHeartbeats 8838000 in
set_option maxHeartbeats 8838000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x0 m hb0 hb2 hb3 h0 h1 h2
  · exact r1l7_10_12_23_L_I_L_R_H_I_x0_x0_x1 m hb0 hb2 hb3 h0 h1 h2

set_option maxHeartbeats 8838000 in
set_option maxHeartbeats 8838000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1230 | h1230
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1231 | h1231
    · linarith only [h0, h1, h1231, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1233 | h1233
      · linarith only [h1231, h1233, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1235 | h1235
        · linarith only [h1231, h1235, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1237 | h1237
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1238 | h1238
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1239 | h1239
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1240 | h1240
                · linarith only [h0, h1231, h1240, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h0, h1, h1240, hc23, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1243 | h1243
                · linarith only [h0, h1, h1243, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h1, h1243, hc23, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h1238, hc35, hlam, hphi, ht23, u2ehi1]
          · linarith only [h0, h1, h1237, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1248 | h1248
    · linarith only [h0, h1, h1248, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1250 | h1250
      · linarith only [h1248, h1250, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1252 | h1252
        · linarith only [h1248, h1252, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1254 | h1254
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1255 | h1255
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1256 | h1256
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1257 | h1257
                · linarith only [h0, h1, h1248, h1257, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h0, h1, h1257, hc23, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1260 | h1260
                · linarith only [h0, h1, h1260, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h1, h1260, hc23, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h1255, hc35, hlam, hphi, ht23, u2ehi1]
          · linarith only [h0, h1, h1254, hc34, hlam, hphi, ht23, u2ehi1]

set_option maxHeartbeats 8838000 in
set_option maxHeartbeats 8838000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_23_L_I_L_R_H_I_x0_x0 m hb0 hb2 hb3 h0 h1
  · exact r1l7_10_12_23_L_I_L_R_H_I_x0_x1 m hb0 hb2 hb3 h0 h1

set_option maxHeartbeats 8838000 in
set_option maxHeartbeats 8838000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  exact r1l7_10_12_23_L_I_L_R_H_I_s0 m hb0 hb2 hb3 h0

set_option maxHeartbeats 8838000 in
set_option maxHeartbeats 8838000 in
theorem r1l7_10_12_23_L_I_L_R_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_23_L_I_L_R_H_I_x0 m hb0 hb2 hb3 h0
  · exact r1l7_10_12_23_L_I_L_R_H_I_x1 m hb0 hb2 hb3 h0

end R2N4
